// ============================================================================
// Expression-level inference functions extracted from InferenceEngine
//
// Plain language: an *expression* is any piece of code that produces a value
// (`1 + 2`, `"hi"`, `obj.field`, `x => x * 2`, `f(3)`, …).  This file is the
// switchboard that, given one expression from the syntax tree, works out its
// type.  It handles the simple kinds directly (literals, arrays, objects,
// operators, template strings) and hands the complicated kinds to specialist
// modules: function expressions → expr-functions.ts, property access →
// expr-member.ts, assignments → expr-assignment.ts, calls → calls.ts.
// ============================================================================

import type * as estree from '../estree';
import {
  Type,
  TRecord,
  TVar,
  tVar,
  tCon,
  tNumber,
  tString,
  tBool,
  tBigInt,
  tNull,
  tUndefined,
  tVoid,
  tArray,
  tRecord,
  tOpenRecord,
  tLabelLit,
  tNumLit,
  isNumLitName,
  tUnion,
  deepMergeTypes,
  tAny,
  tAnyType,
  isAnyType,
  isSpread,
  flattenCurriedType,
  typeToString,
  collectVarNames,
  AstNode,
  T_UNION,
  T_MERGE,
  T_SPREAD_ARRAY,
  T_ARRAY,
  T_FUNCTION,
  T_STRING,
  T_TYPEREP,
  T_TUPLE,
  containsForall,
  tLabelVar,
} from '../hm/types';
import { TypeEnv, instantiate} from '../hm/env';
import { unify, UnificationError } from '../hm/unify';
import { isHiddenPropertyOffset, isBuiltinType} from '../registries/methodRegistry';
import { isDataType, getDataType} from '../registries/dataTypeRegistry';
import { lookupConstraint } from '../registries/constraintRegistry';
import { constraintBaseName } from '../hm/types';
import {
  mergeUnion,
  freshenType,
  mergeSameConstructor,
  structuralEquals,
  someType,
} from '../hm/typeUtils';
import { expandAliases } from './annotations';
import { harvestTaggedTemplateParams } from './call-rows';
import { argumentOutsideParameter } from './unifyDiag';
import {
  computeNarrowedEnvs,
  extractMemberNullCheck,
  extractNullCheck,
  extractTypeofCheck,
  extractTypePredicateNarrowing,
} from './narrowing';
import { findConstructor, exportsToRecord } from './helpers';
import { isUntypedModule } from './types';
import { isRequireCall, getCallMarker, filterUnion, isHasTest } from './narrowing';

import { inferFunctionExpression } from './expr-functions';
import { inferAssignmentExpression, stripUndefinedFromUnion } from './expr-assignment';
import { inferMemberExpression } from './expr-member';
import { inferJSXElement, inferJSXFragment } from './expr-jsx';

import type { InferenceEngine } from './index';

// -----------------------------------------------------------------------
// Expressions
// -----------------------------------------------------------------------

export function inferExpression(engine: InferenceEngine, node: AstNode, env: TypeEnv): Type {
  return inferExpressionWithExpected(engine, node, env, undefined);
}

export function inferExpressionWithExpected(engine: InferenceEngine, node: AstNode, env: TypeEnv, expectedType: Type | undefined): Type {
  const type = inferExpressionInner(engine, node, env, expectedType);
  engine.recordNodeType(node, type);
  return type;
}

export function inferExpressionInner(engine: InferenceEngine, node: AstNode, env: TypeEnv, expectedType?: Type): Type {
  switch (node.type) {
    // --- Literals ---
    case 'Literal':
      return inferLiteral(engine, node, expectedType);

    // --- Identifiers ---
    case 'Identifier':
      return inferIdentifier(engine, node, env, expectedType);

    // --- Binary expressions ---
    case 'BinaryExpression':
      return inferBinaryExpression(engine, node, env);

    // --- Unary expressions ---
    case 'UnaryExpression':
      return inferUnaryExpression(engine, node, env);

    // --- Logical expressions ---
    case 'LogicalExpression':
      return inferLogicalExpression(engine, node, env);

    // --- Function / Arrow functions ---
    case 'ArrowFunctionExpression':
    case 'FunctionExpression':
      return inferFunctionExpression(engine, node, env, expectedType);

    // --- Call expressions ---
    case 'CallExpression': {
      // CommonJS `require ("…")` used as an EXPRESSION (re-export barrels
      // `module.exports = { RTask: require ("./RTask") }`, inline
      // `require ("./x").prop`).  Declaration forms (`const x = require …`)
      // are handled in statements.ts; this mirrors their semantics.
      // Without it, `require` was looked up as a plain variable and every
      // barrel entry reported a misleading "Unbound variable: 'require'".
      if (isRequireCall(node) && !env.lookup('require')) {
        return inferRequireExpression(engine, node as estree.CallExpression);
      }
      // `m.get (k)` after `m.has (k)` (see `presentKeyMarker`): the key is
      // there, so the lookup's `| Undefined` (a miss) goes.  Inferred without
      // the expected type, which the caller compares with the narrowed one.
      {
        const marker = getCallMarker(node);
        if (marker && env.lookup(marker)) {
          const looked = engine.subst.apply(engine.inferCallExpression(node as estree.CallExpression, env));
          const present = filterUnion(looked, m => !(m.tag === 'TCon' && m.name === 'Undefined' && m.args.length === 0));
          engine.recordNodeType(node, present);
          return present;
        }
      }
      return engine.inferCallExpression(node as estree.CallExpression, env, expectedType);
    }

    // --- New expressions (treated like call to constructor) ---
    case 'NewExpression':
      return engine.inferCallExpression(node as unknown as estree.CallExpression, env, expectedType);

    // --- Conditional (ternary) ---
    case 'ConditionalExpression':
      return inferConditionalExpression(engine, node, env, expectedType);

    // --- Array expression ---
    case 'ArrayExpression':
      return inferArrayExpression(engine, node, env, expectedType);

    // --- Object expression ---
    case 'ObjectExpression':
      return inferObjectExpression(engine, node, env, expectedType);

    // --- Assignment ---
    case 'AssignmentExpression':
      return inferAssignmentExpression(engine, node, env);

    // --- Template literal — infer interpolated expressions ---
    case 'TemplateLiteral': {
      for (const expr of (node.expressions ?? [])) {
        inferExpression(engine, expr, env);
      }
      return tString;
    }

    // --- Member expression (simplified) ---
    case 'MemberExpression':
      return inferMemberExpression(engine, node, env);

    // --- this expression ---
    case 'ThisExpression': {
      const thisScheme = env.lookup('this');
      if (thisScheme) {
        const t = instantiate(thisScheme);
        // Rule #1: the signature wins.  When `this` is bound to a method
        // annotation's receiver (`Type a ~> ...`), freeze the receiver at this
        // node so hover renders it with the signature's OWN variable letters
        // instead of re-lettering from the enclosing method scope (which would
        // turn `[a]` into `[b]`).
        if (env.lookup('__signatureThis')) {
          engine.frozenParamType.set(node.start, t);
        }
        return t;
      }
      return tVar();
    }

    // --- Update expression (i++, i--, ++i, --i) ---
    case 'UpdateExpression': {
      const argType = inferExpression(engine, node.argument, env);
      engine.unifyWithDiagnostic(argType, tNumber, node);
      return tNumber;
    }

    // --- Await expression: unwrap Promise<T> → T ---
    case 'AwaitExpression':
      return inferAwaitExpression(engine, node as unknown as estree.AwaitExpression, env);

    // --- Optional chaining: obj?.prop, obj?.[expr], obj?.() ---
    case 'ChainExpression': {
      // ChainExpression wraps a MemberExpression or CallExpression.
      // We infer the inner expression as-is; we do NOT add Undefined to
      // the result because optional-chaining semantics are handled at
      // the property/call level and adding Undefined would cause noise.
      const innerType = inferExpression(engine, node.expression, env);
      return innerType;
    }

    // --- Sequence expression (comma operator): (a, b, c) → type of c ---
    case 'SequenceExpression': {
      let lastType: Type = tVoid;
      for (const expr of (node.expressions ?? [])) {
        lastType = inferExpression(engine, expr, env);
      }
      return lastType;
    }

    // --- Class expression ---
    case 'ClassExpression':
      return inferClassExpression(engine, node as unknown as estree.ClassExpression, env);

    // --- Tagged template expression ---
    case 'TaggedTemplateExpression':
      return inferTaggedTemplateExpression(engine, node as unknown as estree.TaggedTemplateExpression, env);

    // --- Yield expression ---
    case 'YieldExpression': {
      const yieldNode = node as unknown as estree.YieldExpression & { delegate?: boolean };
      const argType = yieldNode.argument
        ? inferExpression(engine, yieldNode.argument as AstNode, env)
        : tUndefined;
      // Record the yielded element type on the enclosing generator frame so
      // `inferFunctionExpression` can model the function's result as
      // `Generator <yield>`.  `yield* iterable` delegates: the contributed
      // element type is the iterable's element, not the iterable itself.
      const frame = engine.generatorYieldStack[engine.generatorYieldStack.length - 1];
      if (frame) {
        frame.push(yieldNode.delegate ? iterableElementType(engine, argType) : argType);
      }
      // The *value* of a `yield`/`yield*` expression (what it evaluates to when
      // the generator is resumed) is unknown to us — model it as a fresh var.
      return tVar();
    }

    // --- MetaProperty: new.target, import.meta ---
    case 'MetaProperty':
      return tVar();

    // --- Dynamic import: import('./mod') -> Promise<{...exports}> ---
    case 'ImportExpression': {
      const src = (node as { source?: AstNode }).source;
      // If the argument is a string literal we can resolve the module via the
      // same import resolver used for static imports — this gives real
      // completion / hover on `(await import('./mod')).foo`.
      if (src && src.type === 'Literal' && typeof (src as estree.Literal).value === 'string' && engine.importResolver) {
        const specifier = (src as estree.Literal).value as string;
        const exportedBindings = engine.importResolver(specifier);
        if (exportedBindings && !isUntypedModule(exportedBindings)) {
          return tCon('Promise', [tVar(), exportsToRecord(exportedBindings)]);
        }
        if (isUntypedModule(exportedBindings)) {
          return tCon('Promise', [tVar(), tVar()]);
        }
      }
      // Fall back to inferring the argument (for diagnostics on non-string
      // sources) and returning Promise<*> for unresolvable specifiers.
      if (src) inferExpression(engine, src, env);
      return tCon('Promise', [tVar(), tAny]);
    }

    // --- JSX (parsed by the Babel backend; see expr-jsx.ts) ---
    case 'JSXElement':
      return inferJSXElement(engine, node, env);
    case 'JSXFragment':
      return inferJSXFragment(engine, node, env);
    case 'JSXExpressionContainer':
      // Reached only when a container is inferred directly (normally its
      // inner expression is extracted by expr-jsx.ts first).
      return node.expression.type === 'JSXEmptyExpression'
        ? tUndefined
        : inferExpression(engine, node.expression, env);
    case 'JSXText':
      return tString;

    default:
      return tVar();
  }
}

// -----------------------------------------------------------------------
// Expression helpers
// -----------------------------------------------------------------------

/** Await expression: unwrap Promise e a → a. */
function inferAwaitExpression(engine: InferenceEngine, node: estree.AwaitExpression, env: TypeEnv): Type {
  const argType = inferExpression(engine, node.argument, env);
  const resolved = engine.subst.apply(argType);
  if (resolved.tag === 'TCon' && resolved.name === 'Promise' && resolved.args.length === 2) {
    return resolved.args[1];
  }
  if (resolved.tag === 'TVar') {
    const innerType = tVar();
    engine.unifyWithDiagnostic(argType, tCon('Promise', [tVar(), innerType]), node);
    return engine.subst.apply(innerType);
  }
  // JS allows awaiting non-promises
  return resolved;
}

/** Class expression: return the constructor type. */
function inferClassExpression(engine: InferenceEngine, node: estree.ClassExpression, env: TypeEnv): Type {
  const classBody: AstNode[] = (node.body as estree.ClassBody)?.body ?? [];
  const constructorMethod = findConstructor(classBody);
  if (constructorMethod) {
    return inferFunctionExpression(engine, (constructorMethod as estree.MethodDefinition).value, env);
  }
  return tVar();
}

/**
 * Tagged template expression — typed as the equivalent call
 * `tag([...strings], ...expressions)`, mirroring the runtime semantics, when
 * the tag's type is known and can absorb the interpolations.  This is what
 * makes annotated template tags (e.g. a query builder's
 * `sql :: ([String], ...) -> SQLTag p o`) produce real result types and
 * thread interpolation types into the tag's signature.
 *
 * Falls back to the historical behavior (infer interpolations for side
 * effects, return a fresh var) when the tag is untyped or its arity cannot
 * accept `strings + interpolations` — plain JS tag helpers often declare only
 * `(strings)`, and routing those through the strict call path would produce
 * spurious arity diagnostics.
 */
function inferTaggedTemplateExpression(engine: InferenceEngine, node: estree.TaggedTemplateExpression, env: TypeEnv): Type {
  const exprs: estree.Expression[] = (node.quasi?.expressions as estree.Expression[]) ?? [];
  const tagType = inferExpression(engine, node.tag, env);
  const resolved = engine.subst.apply(tagType);
  const branches: Type[] = resolved.tag === 'TCon' && resolved.name === T_UNION
    ? resolved.args.map((a) => engine.subst.apply(a))
    : [resolved];

  const canRoute = branches.some((b) => {
    if (b.tag !== 'TFun') return false;
    // Variadic tag `(a, ...) -> r`: absorbs any number of interpolations.
    if (b.param.tag === 'TCon' && b.param.name === T_TUPLE) {
      if (b.param.args.some(isSpread)) return true;
      // Non-variadic tuples take all args at once — no partial application,
      // so the arity must match exactly.
      return b.param.args.length === 1 + exprs.length;
    }
    // Curried form: count parameter slots.
    return flattenCurriedType(b).params.length >= 1 + exprs.length;
  });

  if (canRoute && node.quasi?.quasis) {
    // Synthesize `tag(["s0", "s1", ...], e0, e1, ...)` with source positions
    // taken from the real template parts so diagnostics land on the template.
    const strings = node.quasi.quasis.map((q) => ({
      type: 'Literal',
      value: q.value?.cooked ?? '',
      raw: JSON.stringify(q.value?.cooked ?? ''),
      start: q.start,
      end: q.end,
    }));
    const arrNode = {
      type: 'ArrayExpression',
      elements: strings,
      start: node.quasi.start,
      end: node.quasi.end,
    };
    const callNode = {
      type: 'CallExpression',
      callee: node.tag,
      arguments: [arrNode, ...exprs],
      optional: false,
      start: node.start,
      end: node.end,
    } as unknown as estree.CallExpression;
    const result = engine.inferCallExpression(callNode, env);
    // Params threading for template tags: function interpolations
    // (`sql\`... ${p => p.riziv} ...\``) contribute their accessed fields
    // to the result's parameter slot, mirroring the selector-array
    // harvest in call-rows.
    harvestTaggedTemplateParams(engine, env, callNode, result);
    return result;
  }

  for (const expr of exprs) {
    inferExpression(engine, expr, env);
  }
  return tVar();
}

export function inferLiteral(engine: InferenceEngine, node: estree.Literal, expectedType?: Type): Type {
  const val = node.value;
  if (typeof val === 'bigint') return tBigInt;
  if (typeof val === 'number') {
    // Take the numeric literal type only where exactly that literal is
    // expected (a `2 -> …` overload branch, or a union listing it).
    if (expectedType) {
      const lit = String(val);
      const resolved = engine.resolve(expectedType);
      if (resolved.tag === 'TCon' && resolved.args.length === 0 && isNumLitName(resolved.name)) {
        return tNumLit(val);
      }
      if (resolved.tag === 'TCon' && resolved.name === T_UNION
          && resolved.args.some(m => { const r = engine.resolve(m); return r.tag === 'TCon' && r.name === lit; })) {
        return tNumLit(val);
      }
    }
    return tNumber;
  }
  if (typeof val === 'string') {
    // Promote string literals to label literals when context demands it
    // (e.g. as the label argument of a label-polymorphic function such as
    // `drop2 :: k -> { [k] :: a, ...r } -> { ...r }`).
    //
    // Also promote when the expected position is a Union containing one
    // or more TLabelLit members — this is what makes per-table selector
    // unions work, e.g. `Foo :: ['id' | 'name' | Prop t a | ...] -> ...`
    // accepts `"id"` by matching the label-lit branch of the union, and
    // rejects `"naame"` because no TLabelLit branch matches and no other
    // branch accepts a label.  We promote unconditionally whenever there
    // is *any* TLabelLit in the union (not only when one matches), so a
    // typo like `"naame"` gets a real "Cannot unify" diagnostic instead
    // of being silently absorbed via the TLabel↔String compat rule.
    if (expectedType) {
      const resolved = engine.resolve(expectedType);
      if (resolved.tag === 'TLabel') return tLabelLit(val);
      if (resolved.tag === 'TCon' && resolved.name === T_UNION) {
        let hasLit = false;
        for (const arg of resolved.args) {
          const m = engine.resolve(arg);
          if (m.tag === 'TLabel' && m.kind === 'lit') { hasLit = true; break; }
        }
        if (hasLit) return tLabelLit(val);
      }
    }
    return tString;
  }
  if (typeof val === 'boolean') return tBool;
  if (val === null) return tNull;
  if (val instanceof RegExp) return tCon('RegExp');
  return tVoid;
}

/** True when type variable `id` carries a constraint of kind `* -> *`
 *  (Functor/Monad/… — the variable stands for a type constructor). */
function isHigherKindedVar(engine: InferenceEngine, id: number): boolean {
  const names = engine.kvConstraints.get(id) ?? [];
  return names.some((n) => lookupConstraint(constraintBaseName(n))?.expectedKind === '* -> *');
}

export function inferIdentifier(engine: InferenceEngine, node: estree.Identifier, env: TypeEnv, expectedType?: Type): Type {
  const name = node.name;
  if (name === 'undefined') return tUndefined;
  if (name === 'true' || name === 'false') return tBool;
  if (name === 'NaN' || name === 'Infinity') return tNumber;

  // A registered sumtype *carrier* (`function Maybe(){throw}`) referenced where
  // a `TypeRep m` is expected acts as a *type representative witness*, exactly
  // like a built-in constructor.  Without this the carrier's inferred function
  // type (`() -> ()`) reaches `unifyTypeRep`, whose return-type extraction pins
  // `m = ()` (yielding a spurious `Cannot unify 'Maybe a' with '()'`).  Guarded
  // on an expected `TypeRep …` so member access (`Maybe.of`) and direct calls
  // (`Maybe()`) — which carry no such expectation — keep the carrier binding.
  if (expectedType && /^[A-Z]/.test(name) && isDataType(name)) {
    const expected = engine.resolve(expectedType);
    if (expected.tag === 'TCon' && expected.name === T_TYPEREP) {
      // Apply the carrier to one fresh var per declared type parameter so the
      // witness is at the same kind (`*`) as the values it will be compared
      // against — e.g. `Maybe a`, not the bare `Maybe` (kind `* -> *`), which
      // would clash with `Nothing :: Maybe a` on arity.
      const dt = getDataType(name);
      let args = dt ? dt.decl.typeVars.map(() => tVar()) : [];
      // ...unless the representative stands for a higher-kinded variable
      // (`TypeRep m` under `Monad m`, as in a monad-transformer factory
      // `StateT (Either)`): then the witness is the constructor itself, one
      // argument short (`Either e`), so `m (Pair a s)` re-applies it.
      // Saturating it (`Either e a`) made `m (Pair a s)` ill-kinded.
      const inner = engine.resolve(expected.args[0]);
      if (inner.tag === 'TVar' && args.length > 0 && isHigherKindedVar(engine, inner.id)) {
        args = args.slice(0, -1);
      } else if (inner.tag === 'TCon' && inner.name === name && inner.args.length < args.length) {
        // The expected representative is already a (partial) application of
        // this constructor — e.g. an annotation `TypeRep (FutureT (Either l) e)`
        // flowed into `FutureT (Either)` and fixed `m := Either l` first.
        // Match its arity instead of saturating.
        args = args.slice(0, inner.args.length);
      }
      const witness = tCon(T_TYPEREP, [tCon(name, args)]);
      engine.recordNodeType(node, witness);
      return witness;
    }
  }

  const scheme = env.lookup(name);
  if (!scheme) {
    // A built-in type constructor referenced in value position (e.g.
    // `id(Function)`, `of(String)`) acts as a *type representative witness*:
    // the global object stands in for its type constructor.  Give it the type
    // `TypeRep <Name>` so it satisfies a `TypeRep f` parameter.
    if (/^[A-Z]/.test(name) && isBuiltinType(name)) {
      // `Function` represents the reader functor `Function [x]` (one fixed
      // argument type, like `Either e`), so `chainRec (Function)` yields an
      // applied `Function [x] b` — a real function type.
      if (name === T_FUNCTION) return tCon(T_TYPEREP, [tCon(T_FUNCTION, [tCon(T_ARRAY, [tVar()])])]);
      return tCon(T_TYPEREP, [tCon(name)]);
    }
    // A free identifier that has no binding but is declared as a value in the
    // project globals file (e.g. a `jest.hm` declaring `describe :: ...`)
    // resolves to that global signature.  Only plain value annotations from
    // the globals file qualify — method/receiver annotations (`Type#m`) and
    // local annotations are excluded so this stays a genuine global binding.
    const globalAnn = engine.annotationMap.get(name);
    if (globalAnn && globalAnn.origin === 'globals' && globalAnn.scheme
        && !globalAnn.receiver && !globalAnn.error
        && !name.includes('#') && !name.includes('.')) {
      const result = engine.instantiateWithConstraints(globalAnn.scheme, node);
      engine.recordNodeType(node, result);
      return result;
    }
    engine.addDiag(`Unbound variable: '${name}'`, node);
    engine.unboundIdentifiers.add(node.start);
    return tVar();
  }
  // Mark reference sites of curried variables so signature help can detect them
  if (scheme.isCurriedResult) {
    engine.curriedNodes.add(node.start);
  }
  const result = engine.instantiateWithConstraints(scheme, node);
  engine.recordNodeType(node, result);
  // A reference to an annotated parameter must display the signature form, not
  // the body-poisoned substitution.  The param's binding carries `frozenDisplay`
  // (the annotation); control-flow narrowing rebinds the name via plain `mono`,
  // dropping it, so a reference inside an accepted narrow still shows the
  // narrowed type.
  if (scheme.frozenDisplay) {
    engine.frozenParamType.set(node.start, scheme.frozenDisplay);
  }
  return result;
}

/** Unify both operands of a numeric binary expression with Number. */
export function requireNumericOperands(engine: InferenceEngine, left: Type, right: Type, node: estree.BinaryExpression): void {
  engine.unifyWithDiagnostic(left, tNumber, node.left);
  engine.unifyWithDiagnostic(right, tNumber, node.right);
}

/**
 * Relational operators (`<`, `>`, `<=`, `>=`) in JS are not Number-only: they
 * also compare Strings lexicographically (and, via valueOf, other ordered
 * values).  We therefore do NOT force the operands to Number.  Instead we make
 * the two sides agree with each other (so beneficial inference still flows),
 * but SWALLOW a unification failure the same way `===` does — a heterogeneous
 * comparison is legal JS and must not raise a type error.  This fixes
 * `String <= String` wrongly reporting `Cannot unify 'String' with 'Number'`.
 */
export function relateComparableOperands(engine: InferenceEngine, left: Type, right: Type): void {
  try {
    engine.subst.mergeFrom(unify(engine.resolve(left), engine.resolve(right)));
  } catch (e) {
    if (!(e instanceof UnificationError)) throw e;
    // Heterogeneous comparison — no diagnostic.
  }
}

/**
 * Element type of an iterable value type, used for `yield* iterable` and
 * `for…of`.  Arrays / typed-array-likes / Generator / Set expose their element
 * as their single type argument; a String iterates over Strings; anything else
 * contributes a fresh variable so inference stays permissive.
 */
export function iterableElementType(engine: InferenceEngine, t: Type): Type {
  const r = engine.subst.apply(t);
  if (r.tag === 'TCon') {
    if (r.name === T_STRING) return tString;
    if (r.args.length === 1) return r.args[0];
  }
  return tVar();
}

export function inferBinaryExpression(engine: InferenceEngine, node: estree.BinaryExpression, env: TypeEnv): Type {
  const left = inferExpression(engine, node.left, env);
  const right = inferExpression(engine, node.right, env);
  const op: string = node.operator;

  switch (op) {
    // Arithmetic
    case '+': {
      // + is polymorphic in JS:
      //   String + any = String  (concatenation)
      //   any + String = String  (concatenation)
      //   Number + Number = Number (arithmetic)
      const resolvedLeft = engine.subst.apply(left);
      const resolvedRight = engine.subst.apply(right);
      if (
        (resolvedLeft.tag === 'TCon' && resolvedLeft.name === T_STRING) ||
        (resolvedRight.tag === 'TCon' && resolvedRight.name === T_STRING)
      ) {
        // At least one side is String → result is String (JS coercion)
        return tString;
      }
      // Otherwise default to number addition
      requireNumericOperands(engine, left, right, node);
      return tNumber;
    }
    case '-':
    case '*':
    case '/':
    case '%':
    case '**':
      requireNumericOperands(engine, left, right, node);
      return tNumber;

    // Strict equality — JS reference/value equality is heterogeneous: any two
    // values may be compared (e.g. comparing a value of type `(* -> a)` with
    // one of type `(* -> b)`, or two distinct rigid skolems). We attempt to
    // unify the operands so that beneficial inference still happens (e.g.
    // `s === ""` refines `s` to String), but we SWALLOW a unification failure
    // instead of reporting a mismatch. This stays sound w.r.t. type-class
    // constraints: constraints are validated post-hoc against each variable's
    // resolved concrete type (see validatePendingConstraints), not by unify,
    // so a swallowed structural failure can never hide a constraint diagnostic.
    case '===':
    case '!==':
      try {
        engine.subst.mergeFrom(unify(engine.resolve(left), engine.resolve(right)));
      } catch (e) {
        if (!(e instanceof UnificationError)) throw e;
        // Heterogeneous comparison — no diagnostic.
      }
      return tBool;

    // Loose equality — JS allows comparing any two values with coercion,
    // so we do NOT unify the operands.
    case '==':
    case '!=':
      return tBool;

    case '<':
    case '>':
    case '<=':
    case '>=':
      relateComparableOperands(engine, left, right);
      return tBool;

    // Bitwise
    case '|':
    case '&':
    case '^':
    case '<<':
    case '>>':
    case '>>>':
      requireNumericOperands(engine, left, right, node);
      return tNumber;

    // instanceof operator
    case 'instanceof':
      return tBool;

    // in operator (key in object)
    case 'in':
      return tBool;

    default:
      return tVar();
  }
}

export function inferUnaryExpression(engine: InferenceEngine, node: estree.UnaryExpression, env: TypeEnv): Type {
  const arg = inferExpression(engine, node.argument, env);
  switch (node.operator) {
    case '-':
    case '+':
    case '~':
      engine.unifyWithDiagnostic(arg, tNumber, node.argument);
      return tNumber;
    case '!':
      return tBool;  // ! always returns Boolean, argument can be any type
    case 'typeof':
      return tString;
    case 'void':
      return tVoid;
    case 'delete':
      return tBool;
    default:
      return tVar();
  }
}

export function inferLogicalExpression(engine: InferenceEngine, node: estree.LogicalExpression, env: TypeEnv): Type {
  const left = inferExpression(engine, node.left, env);
  const op: string = node.operator;

  if (op === '??') {
    // Nullish coalescing: left ?? right — see `defaultedType`.
    const right = inferExpression(engine, node.right, env);
    return defaultedType(engine, node.left as AstNode, left, right);
  }

  if (op === '||') {
    // Logical OR: left || right.
    // When `left` is a bare identifier, narrow it for `right`'s env to its
    // falsy refinement, and compute the result as `truthyLeft | right` (so
    // `value || "x"` where value :: String | Undefined returns String,
    // not String | Undefined).  Identifier-LHS only to avoid the
    // typeof/null cascade surprises seen in `typeof x === 'object' && x !== null`.
    if (node.left.type === 'Identifier') {
      const narrowed = computeNarrowedEnvs(engine.subst, node.left, env, engine.annotationMap);
      const right = inferExpression(engine, node.right, narrowed.altEnv);
      const truthyScheme = narrowed.consEnv.lookup((node.left as estree.Identifier).name);
      const truthyLeft = truthyScheme ? engine.subst.apply(truthyScheme.type) : left;
      return tUnion([truthyLeft, right]);
    }
    const right = inferExpression(engine, node.right, narrowForOrRight(engine, node.left as AstNode, env));
    return defaultedType(engine, node.left as AstNode, left, right);
  }

  if (op === '&&') {
    // Logical AND: left && right
    // When `left` is a bare identifier, narrow it (e.g. remove Undefined
    // from a union) in the env used to infer `right`.  Only Identifier-LHS
    // is narrowed here — see comment on `||` above.
    const rightEnv = narrowForAndRight(engine, node.left as AstNode, env);
    const right = inferExpression(engine, node.right, rightEnv);
    return right;
  }

  inferExpression(engine, node.right, env);
  return tBool;
}

/**
 * Result of a default expression `left ?? right` / `left || right` (the
 * latter for a non-identifier left; identifiers are narrowed above).
 *  - `left` is an unknown FIELD (`p.from`, still a type variable): the field
 *    becomes optional, `right | Undefined`, and the result is `right`.  A
 *    default says the field may be absent and what type it has —
 *    `startsAt.gte (p => p.from ?? new Date ())` gives `from :: Date |
 *    Undefined`, and `p => p.from || 2` makes the `2` meet the `Date` the
 *    callback must return, instead of disappearing;
 *  - otherwise `Undefined`/`Null` are dropped from `left` and the result is
 *    `left | right` (both may be returned at runtime).
 */
function defaultedType(engine: InferenceEngine, leftNode: AstNode, left: Type, right: Type): Type {
  const l = engine.resolve(left);
  const r = engine.resolve(right);
  if (l.tag === 'TVar' && leftNode.type === 'MemberExpression') {
    try {
      engine.subst.mergeFrom(unify(l, tUnion([r, tUndefined])));
      return r;
    } catch { /* fall through to the union */ }
  }
  const present = stripNullish(l);
  if (present === null) return r;
  // `Any | x` is `Any`: an unknown left side may be returned as is.
  if (isAnyType(present) || isAnyType(r)) return tAnyType;
  try {
    const s = unify(present, r);
    engine.subst.mergeFrom(s);
    return engine.resolve(r);
  } catch {
    return mergeUnion(present, r);
  }
}

/** `t` without `Undefined`/`Null` members; null when nothing remains. */
function stripNullish(t: Type): Type | null {
  const isNullish = (x: Type) => x.tag === 'TCon' && (x.name === 'Undefined' || x.name === 'Null');
  if (isNullish(t)) return null;
  if (t.tag !== 'TCon' || t.name !== T_UNION) return t;
  const kept = t.args.filter(a => !isNullish(a));
  if (kept.length === 0) return null;
  return kept.length === 1 ? kept[0] : tUnion(kept);
}

/** A string literal, or a ternary whose branches all are (`ok ? "success"
 *  : failed ? "danger" : "primary"`): such an expression meets an expected
 *  literal union with its literals. */
function isStringLiteralChoice(node: AstNode): boolean {
  if (node.type === 'Literal') return typeof (node as unknown as estree.Literal).value === 'string';
  if (node.type !== 'ConditionalExpression') return false;
  const c = node as unknown as estree.ConditionalExpression;
  return isStringLiteralChoice(c.consequent as AstNode) && isStringLiteralChoice(c.alternate as AstNode);
}

export function inferConditionalExpression(engine: InferenceEngine, node: estree.ConditionalExpression, env: TypeEnv, expectedType?: Type): Type {
  inferExpression(engine, node.test, env);

  const { consEnv, altEnv } = computeNarrowedEnvs(engine.subst, node.test, env, engine.annotationMap);

  // A string-literal branch gets the expected type, so
  // `paint (ok ? "success" : "danger")` meets a literal union with its
  // literals (other branches keep their own inference).
  const branch = (b: estree.Expression, branchEnv: TypeEnv): Type =>
    expectedType && isStringLiteralChoice(b as AstNode)
      ? inferExpressionWithExpected(engine, b as AstNode, branchEnv, expectedType)
      : inferExpression(engine, b, branchEnv);
  const consType = branch(node.consequent, consEnv);
  const altType = branch(node.alternate, altEnv);

  try {
    const s = unify(engine.resolve(consType), engine.resolve(altType));
    engine.subst.mergeFrom(s);
    // Unification also succeeds when one branch is a MEMBER of the other's
    // union (`c ? null : f (x)` with `f x :: String | Null`): the result is
    // then the union, not the narrower branch.
    const rc = engine.resolve(consType);
    const ra = engine.resolve(altType);
    const isUnionT = (t: Type): boolean => t.tag === 'TCon' && t.name === T_UNION;
    if ((isUnionT(rc) || isUnionT(ra)) && !structuralEquals(rc, ra)) return mergeUnion(rc, ra);
    // The same holds per field of two records: `p == null ? { from: undefined }
    // : p` with `p :: { from :: Date | Undefined }` is the wider record, not
    // the literal's `{ from :: Undefined }`.
    if (rc.tag === 'TRecord' && ra.tag === 'TRecord' && !structuralEquals(rc, ra)) return widenRecordBranches(rc, ra);
    return consType;
  } catch (e) {
    if (e instanceof UnificationError) {
      const rc = engine.resolve(consType);
      const ra = engine.resolve(altType);
      // Try merging same-name parameterized types before falling back to flat union
      const merged = mergeSameConstructor(rc, ra);
      if (merged) return merged;
      return mergeUnion(rc, ra);
    }
    throw e;
  }
}

/** The record type of a conditional whose branches unified: per field the
 *  union when one branch's field is a member of the other's union (nested
 *  records field by field).  Keeps the alias of a branch that already is
 *  the result, so `c ? { … } : plan` still displays as `Plan`. */
function widenRecordBranches(a: TRecord, b: TRecord): TRecord {
  const isUnionT = (t: Type): boolean => t.tag === 'TCon' && t.name === T_UNION;
  const fields: Record<string, Type> = {};
  for (const key of Object.keys(a.fields)) {
    const fa = a.fields[key];
    const fb = b.fields[key];
    if (fb === undefined || structuralEquals(fa, fb)) fields[key] = fa;
    else if (isUnionT(fa) || isUnionT(fb)) fields[key] = mergeUnion(fa, fb);
    else if (fa.tag === 'TRecord' && fb.tag === 'TRecord') fields[key] = widenRecordBranches(fa, fb);
    else fields[key] = fa;
  }
  for (const key of Object.keys(b.fields)) {
    if (!(key in fields)) fields[key] = b.fields[key];
  }
  const widened: TRecord = { tag: 'TRecord', fields, ...(a.rest ? { rest: a.rest } : {}) };
  if (structuralEquals(widened, b)) return b;
  if (structuralEquals(widened, a)) return a;
  return widened;
}

function hasSpreadElementBelow(node: estree.ArrayExpression): boolean {
  for (const e of node.elements) {
    if (e !== null && (e as AstNode).type === 'SpreadElement') return true;
  }
  return false;
}

export function inferArrayExpression(engine: InferenceEngine, node: estree.ArrayExpression, env: TypeEnv, expectedType?: Type): Type {  // If the expected type is Array<X>, seed the element type from the
  // annotation so that elements unify against the expected element type
  // rather than each other.  This allows annotated union element types
  // like [Either String (Number | String)] even when auto-union is
  // suppressed during annotation checking.
  let elemType: Type;
  const resolved = expectedType ? engine.subst.apply(expectedType) : undefined;

  // If the expected type is `Any` (e.g. the array is an argument to a
  // call whose callee resolved to `Any`, as happens when destructuring
  // from a fully opaque source like `tables.organisation`), each element
  // is checked independently against `Any` instead of being unified
  // against a shared element TVar.  Without this, mixed-shape literals
  // such as `[Limit(5), "id", Prop("name")]` would fail because the
  // first element's type would pin the shared element slot.
  if (resolved && isAnyType(resolved)) {
    for (const elem of node.elements) {
      if (elem) inferExpressionWithExpected(engine, elem as AstNode, env, tAny);
    }
    engine.recordNodeType(node, tArray(tAny));
    return tArray(tAny);
  }

  // Positional spread-array expected: [a, b, ..., z] or [a, b]
  // Each array literal element gets the corresponding positional type so
  // mixed-type literals like ["3", 3] match [String, Number].
  if (resolved && resolved.tag === 'TCon' && resolved.name === T_SPREAD_ARRAY) {
    const expArgs = resolved.args;
    const spreadIdx = expArgs.findIndex(isSpread);
    const before = spreadIdx >= 0 ? expArgs.slice(0, spreadIdx) : expArgs.slice();
    const after = spreadIdx >= 0 ? expArgs.slice(spreadIdx + 1) : [];
    const elements = node.elements;
    const totalElems = elements.length;

    // Arity check
    if (spreadIdx < 0) {
      // Fixed positional: must match exactly
      if (totalElems !== before.length) {
        engine.addDiag(
          `Array literal has ${totalElems} element${totalElems === 1 ? '' : 's'}, expected ${before.length} for type '${typeToString(resolved)}'`,
          node,
        );
      }
    } else {
      // With spread: must have at least before+after elements
      const minRequired = before.length + after.length;
      if (totalElems < minRequired) {
        engine.addDiag(
          `Array literal has ${totalElems} element${totalElems === 1 ? '' : 's'}, expected at least ${minRequired} for type '${typeToString(resolved)}'`,
          node,
        );
      }
    }

    for (let i = 0; i < totalElems; i++) {
      const elem = elements[i];
      if (!elem) continue;
      let expectedElem: Type | undefined;
      if (i < before.length) {
        expectedElem = before[i];
      } else if (spreadIdx >= 0) {
        const idxFromEnd = totalElems - 1 - i;
        if (idxFromEnd >= 0 && idxFromEnd < after.length) {
          expectedElem = after[after.length - 1 - idxFromEnd];
        }
      }
      const t = expectedElem
        ? inferExpressionWithExpected(engine, elem as AstNode, env, expectedElem)
        : inferExpression(engine, elem, env);
      if (expectedElem) {
        engine.unifyWithDiagnostic(t, expectedElem, elem);
      }
    }
    // Build a representative Array type for hover/display: pick the first
    // non-spread element type, freshened so we don't alias the annotation.
    const firstNonSpread = expArgs.find(a => !isSpread(a));
    const arrayElemType = firstNonSpread ? freshenType(firstNonSpread) : tVar();
    engine.recordNodeType(node, tArray(engine.subst.apply(arrayElemType)));
    // Return the resolved SpreadArray type so it unifies with the param slot
    // at the call site (Array<X> would not unify with SpreadArray<...>).
    return engine.subst.apply(resolved);
  }

  // Track the original (un-expanded) element type so the array literal's
  // returned type uses the alias name (`[Selector]`) when one was provided
  // — element-by-element unification still happens against the expanded
  // union to allow heterogeneous element types.
  let originalElemType: Type | undefined;
  let aliasWasExpanded = false;
  // When the expected element type is (or expands to) a Union containing
  // free TVars (e.g. `Prop a | QueryTag a | Table b | ...` from a per-table
  // Selector alias), freshen those TVars per element so distinct elements
  // can match distinct branches with distinct type-arg bindings.  This
  // covers two cases:
  //   • alias still in TCon form (handled via maybeExpandAlias)
  //   • alias eagerly expanded into the annotation already (we must
  //     freshen the expanded union ourselves per element)
  let unionWithFreeVars = false;
  if (resolved && resolved.tag === 'TCon' && resolved.name === T_ARRAY && resolved.args.length === 1) {
    originalElemType = resolved.args[0];
    elemType = resolved.args[0];
    // If the expected element type is a zero-arg type alias (e.g.
    // `[Selector]` where `Selector :: String | Prop a | ...`), expand
    // it so element unification sees the underlying union and can
    // accept heterogeneous element types.
    const expanded = engine.maybeExpandAlias(elemType);
    if (expanded !== elemType) aliasWasExpanded = true;
    elemType = expanded;
    // Union element types can carry alias *members* (e.g.
    // `[UserSelector | Limit p]` where `UserSelector :: "id" | "name"`),
    // and generators emit parameterized aliases (`[UserSelector p]`).
    // `maybeExpandAlias` only expands bare zero-arg aliases, so expand the
    // remaining alias references here.  Free vars introduced by the
    // expansion are picked up by the `unionWithFreeVars` detection below
    // (per-element freshening with result-pinned vars kept shared).
    if (elemType.tag === 'TCon' &&
        (elemType.name === T_UNION || elemType.args.length > 0)) {
      const hasAliasRef = someType(elemType, (n) =>
        n.tag === 'TCon' && n.name !== T_UNION && engine.typeAliases.has(n.name));
      if (hasAliasRef) {
        const fullyExpanded = expandAliases(
          engine.typeAliases, elemType, undefined, engine.typeAliasVars);
        if (fullyExpanded !== elemType) {
          // Re-flatten in case an alias member expanded into a nested union.
          elemType = fullyExpanded.tag === 'TCon' && fullyExpanded.name === T_UNION
            ? tUnion(fullyExpanded.args)
            : fullyExpanded;
        }
      }
    }
    // Detect the eagerly-expanded case: the resolved element type is
    // already a Union containing free TVars (parameter slot was expanded
    // by `expandAnnotationAliases` before instantiation, so the
    // alias-freshening code path above never fires).
    if (!aliasWasExpanded && elemType.tag === 'TCon' && elemType.name === T_UNION) {
      const ids = new Map<number, string>();
      collectVarNames(elemType, ids);
      // Only freshen TVars that aren't bound in the current substitution
      // (i.e. genuinely free at this use site).
      let hasFree = false;
      for (const id of ids.keys()) {
        if (engine.subst.lookup(id) === undefined) { hasFree = true; break; }
      }
      if (hasFree) unionWithFreeVars = true;
    }
  } else {
    elemType = tVar();
  }
  // Detect the "expected element type is a free TVar" case (e.g. callee
  // signature `[b]` with b unbound).  When that holds, allow the array
  // literal to have heterogeneous element types: collect each element's
  // inferred type and bind the TVar to a union of those types in one
  // shot.  Otherwise the per-element unification against the shared
  // `elemType` would pin it to the first element's type and reject every
  // subsequent element of a different type — even though `b` was free
  // and could legitimately be a union.  Constraint validation against a
  // resolved TUnion is enforced separately in
  // `validatePendingUnionConstraints` (every member must satisfy the
  // constraint, not just one).
  let elemTypeIsFreeTVar = false;
  if (resolved && !aliasWasExpanded && !unionWithFreeVars) {
    const pruned = engine.subst.apply(elemType);
    if (pruned.tag === 'TVar') {
      elemTypeIsFreeTVar = true;
    }
  }
  // No-expected-type fallback widening (cross-tag mixes): when the array
  // has no expected element type and no spread element (a spread imports
  // its element type from a typed source whose stricter type should be
  // honoured by the surrounding literal — see the
  // `Class##field annotation enforces type at private assignment site`
  // regression test), enable a try/rollback strategy below: do the
  // strict per-element unify first to give the existing auto-union /
  // mergeSameConstructor logic a chance to merge cleanly; if any
  // diagnostic fires from that pass, roll back the substitution and the
  // emitted diagnostics, then bind elemType to the union of inferred
  // element types (cross-tag widening like `[1, [2,3]]` →
  // `[Number | [Number]]`, `[function(){}, 1]` → `[Number | (() -> ())]`).
  const tryNoExpectedWidening = !resolved && !hasSpreadElementBelow(node);
  const substSnapshot = tryNoExpectedWidening ? engine.subst.snapshot() : null;
  // Indices of diagnostics emitted by the per-element `unifyWithDiagnostic`
  // below.  Only THOSE are rolled back by the cross-tag widening pass:
  // diagnostics emitted while inferring the elements themselves (e.g. a
  // missing-field error inside a nested call like `[f(), g({})]`) are
  // genuine and must survive the rollback.
  const unifyDiagIndices: number[] = [];
  // First pass: infer each element and collect resolved types so we can
  // merge heterogeneous closed-record element shapes below.  The plain
  // element-by-element unification with a shared `elemType` is lenient
  // for closed records (only common keys are unified), which means the
  // callback in `[{a, b}, {a, c}].map(x => …)` would see `x :: { a }`
  // and the surplus fields disappear.  We post-process the literal to
  // merge all field names across element records, with `T | Undefined`
  // for fields that are missing from at least one element — matching JS
  // runtime semantics where missing keys read as `undefined`.
  const elemTypes: Type[] = [];
  for (const elem of node.elements) {
    if (elem) {
      // For element-type unions originating from an expanded alias
      // (e.g. `Selector :: String | Prop a | ...`), re-instantiate fresh
      // type variables for each element so distinct elements can match
      // distinct branches with distinct type-arg bindings (e.g. one
      // element matches `Prop String`, another `Prop Number`).
      const perElemExpected = aliasWasExpanded && originalElemType
        ? engine.maybeExpandAlias(originalElemType)
        : unionWithFreeVars
          ? freshenType(elemType, engine.pinnedElementVarIds ?? undefined)
          : elemType;
      // Only forward the expected element type into inference for
      // *literal* elements — those are the ones that can be promoted
      // (e.g. a string literal becoming a TLabelLit when the expected
      // element type contains a label-literal).  Forwarding the expected
      // type into arbitrary expressions (call sites, identifiers) would
      // over-constrain return-type unification (cf. auto-union of
      // `[WLeft("foo"), WRight(10), WRight("bar")]`).
      // A ternary of literals (`flag ? "id" : "name"`, also nested) gets it too.
      const isLiteralElem = (elem as AstNode).type === 'Literal' || isStringLiteralChoice(elem as AstNode);
      // Skip forwarding the (free) shared TVar to literal inference too —
      // it would just bind the TVar to the first literal's type and then
      // the next literal would fail unification against it.
      const t = isLiteralElem && !elemTypeIsFreeTVar
        ? inferExpressionWithExpected(engine, elem as AstNode, env, perElemExpected)
        : inferExpression(engine, elem, env);
      if (!elemTypeIsFreeTVar) {
        const beforeUnify = engine.diagnostics.length;
        engine.unifyWithDiagnostic(t, perElemExpected, elem);
        // An element of a list with an expected type must fit it, in that
        // direction (a `String` is not one of `'id' | 'name'`), as a call
        // argument must.
        if (resolved && engine.diagnostics.length === beforeUnify) {
          const outside = argumentOutsideParameter(engine, t, perElemExpected);
          if (outside) engine.addDiag(outside, elem as AstNode);
        }
        if (tryNoExpectedWidening) {
          for (let i = beforeUnify; i < engine.diagnostics.length; i++) {
            unifyDiagIndices.push(i);
          }
        }
      }
      elemTypes.push(engine.subst.apply(t));
    } else {
      elemTypes.push(tUndefined);
    }
  }
  // Free-TVar widening: bind the parameter's element TVar to the union
  // of inferred element types, deduped structurally.  When all elements
  // agree this is a no-op (single-member unions degrade to that member);
  // when they differ, the TVar resolves to `T1 | T2 | ...`.
  if (elemTypeIsFreeTVar && elemTypes.length > 0) {
    const unique: Type[] = [];
    for (const et of elemTypes) {
      if (!unique.some(u => structuralEquals(u, et))) unique.push(et);
    }
    const widened = unique.length === 1 ? unique[0] : tUnion(unique);
    engine.unifyWithDiagnostic(elemType, widened, node);
  }
  // Cross-tag widening (no expected type, no spread): if the strict
  // per-element unification above produced one or more diagnostics
  // (e.g. `[1, [2,3]]` → "Cannot unify '[Number]' with 'Number'"), roll
  // back the substitution and the emitted diagnostics, then bind elemType
  // to the union of inferred element types so the literal types as
  // `[Number | [Number]]` instead.  Annotated arrays are protected: the
  // `tryNoExpectedWidening` flag is false when an expected type is in
  // play, and a spread element disables widening so annotation-derived
  // element types still get strict-checked against sibling literals
  // (cf. the `Class##field` regression test).
  if (tryNoExpectedWidening && substSnapshot &&
      unifyDiagIndices.length > 0) {
    engine.subst.restore(substSnapshot);
    for (let i = unifyDiagIndices.length - 1; i >= 0; i--) {
      engine.diagnostics.splice(unifyDiagIndices[i], 1);
    }
    // Re-resolve element types under the rolled-back substitution.
    const widenedElems = elemTypes.map(t => engine.subst.apply(t));
    const unique: Type[] = [];
    for (const et of widenedElems) {
      if (!unique.some(u => structuralEquals(u, et))) unique.push(et);
    }
    const widened = unique.length === 1 ? unique[0] : tUnion(unique);
    engine.unifyWithDiagnostic(elemType, widened, node);
    // Refresh elemTypes so the closed-record-merge pass below sees the
    // post-rollback shapes.
    elemTypes.splice(0, elemTypes.length, ...widenedElems);
  }
  // Try to merge closed-record element shapes when the array literal
  // mixes records with differing field sets.  Only kicks in when:
  //   • there's no expected element type (otherwise the expectation wins)
  //   • there are >= 2 elements all resolving to closed TRecords
  //   • the field-name sets are not all identical
  if (!resolved && elemTypes.length >= 2) {
    const allClosedRecords = elemTypes.every(
      t => t.tag === 'TRecord' && !t.rest,
    );
    if (allClosedRecords) {
      const records = elemTypes as Array<Extract<Type, { tag: 'TRecord' }>>;
      const allKeys = new Set<string>();
      for (const r of records) for (const k of Object.keys(r.fields)) allKeys.add(k);
      const sameShape = records.every(r => {
        const ks = Object.keys(r.fields);
        return ks.length === allKeys.size && ks.every(k => allKeys.has(k));
      });
      if (!sameShape) {
        const mergedFields: Record<string, Type> = {};
        for (const k of allKeys) {
          const present: Type[] = [];
          let missing = false;
          for (const r of records) {
            if (k in r.fields) present.push(engine.subst.apply(r.fields[k]));
            else missing = true;
          }
          // Deduplicate present types so `String | String` stays `String`.
          const valueType = present.length === 1 ? present[0] : tUnion(present);
          mergedFields[k] = missing ? tUnion([valueType, tUndefined]) : valueType;
        }
        const merged = tRecord(mergedFields);
        // Replace elemType so the array's element type carries the merged
        // shape — used by Array.prototype.map, hover, and completion.
        elemType = merged;
        // Re-record each element node's type under the merged shape so
        // hovering an inline literal also shows the unified view.
        for (let i = 0; i < node.elements.length; i++) {
          const e = node.elements[i];
          if (e) engine.recordNodeType(e as AstNode, merged);
        }
      }
    }
  }
  const finalElem = originalElemType ?? engine.subst.apply(elemType);
  // An empty array literal `[]` carries no element information.  Flag its
  // (unbound) element var as `emptyArray` so (1) union dedup can collapse
  // members differing only in such a var (see `TVar.emptyArray`), and (2) a
  // strict-empty array annotation `[]` accepts this literal.  Applies whether
  // or not an expected element type was present (the expected var, if any, is
  // a throwaway fresh var of this instantiation).
  if (node.elements.length === 0 && finalElem.tag === 'TVar') {
    (finalElem as TVar).emptyArray = true;
  }
  return tArray(finalElem);
}

export function inferObjectExpression(engine: InferenceEngine, node: estree.ObjectExpression, env: TypeEnv, expectedType?: Type): Type {
  // Rank-N: when the expected (annotated) record declares a `forall` field,
  // the corresponding literal property must be checked by SUBSUMPTION — a
  // plain unify would silently instantiate the quantifier and accept a
  // monomorphic value.  Resolve the expected record once up-front.
  // Perf: `containsForall` is a cheap allocation-free scan that guards the
  // substitution/alias work, so the rank-1 hot path pays one tag walk and no
  // allocations.  (A `forall` field hidden behind an unexpanded alias TCon is
  // not seen here and falls back to the lenient legacy unify path.)
  let expectedRecord: Type | undefined;
  if (expectedType && containsForall(expectedType)) {
    const resolvedExpected = engine.maybeExpandAlias(engine.subst.apply(expectedType));
    if (resolvedExpected.tag === 'TRecord'
        && Object.values(resolvedExpected.fields).some(f => engine.subst.apply(f).tag === 'TForall')) {
      expectedRecord = resolvedExpected;
    }
  }
  // Inline function values (`{ render: () => … }`, a JSX child callback)
  // get the expected field type, like an inline function argument does: a
  // callback that ignores trailing parameters is fine in JS, and the
  // function-literal inference pads it to the expected shape.  Resolved
  // lazily, only when a property value is a function literal.
  let expectedFields: Record<string, Type> | null | undefined;
  const expectedFunctionField = (key: string): Type | undefined => {
    if (!expectedType) return undefined;
    if (expectedFields === undefined) {
      const r = engine.maybeExpandAlias(engine.subst.apply(expectedType));
      expectedFields = r.tag === 'TRecord' ? r.fields : null;
    }
    if (!expectedFields || !(key in expectedFields)) return undefined;
    const field = engine.subst.apply(expectedFields[key]);
    if (field.tag === 'TFun') return field;
    // An optional callback (`(a -> b) | Undefined`): its single function member.
    if (field.tag === 'TCon' && field.name === T_UNION) {
      const fns = field.args.filter(a => engine.subst.apply(a).tag === 'TFun');
      if (fns.length === 1) return engine.subst.apply(fns[0]);
    }
    return undefined;
  };
  // A string literal value gets the expected field type when that type
  // lists string literals (`intent :: Intent | Undefined` with
  // `Intent :: "none" | "primary" | …`), like a literal argument does:
  // `{ intent: "succes" }` is then a typo, not a `String`.  Aliases inside
  // the union are expanded so `inferLiteral` sees the literal members.
  const expectedLiteralField = (key: string): Type | undefined => {
    if (!expectedType) return undefined;
    if (expectedFields === undefined) {
      const r = engine.maybeExpandAlias(engine.subst.apply(expectedType));
      expectedFields = r.tag === 'TRecord' ? r.fields : null;
    }
    if (!expectedFields || !(key in expectedFields)) return undefined;
    const members: Type[] = [];
    const collect = (t: Type, depth: number): void => {
      const r = engine.maybeExpandAlias(engine.subst.apply(t));
      if (depth < 4 && r.tag === 'TCon' && r.name === T_UNION) {
        for (const a of r.args) collect(a, depth + 1);
      } else {
        members.push(r);
      }
    };
    collect(expectedFields[key], 0);
    if (!members.some(m => m.tag === 'TLabel' && m.kind === 'lit')) return undefined;
    return tUnion(members);
  };
  // A nested object literal gets the expected field type when that is a
  // record (or `Record | Undefined`), like an object literal argument does
  // (`drawerProps={{ position: "left", onClose: () => close () }}`): its
  // callbacks then get their parameter types and its string literals the
  // literal union.
  const expectedRecordField = (key: string): Type | undefined => {
    if (!expectedType) return undefined;
    if (expectedFields === undefined) {
      const r = engine.maybeExpandAlias(engine.subst.apply(expectedType));
      expectedFields = r.tag === 'TRecord' ? r.fields : null;
    }
    if (!expectedFields || !(key in expectedFields)) return undefined;
    const field = engine.maybeExpandAlias(engine.subst.apply(expectedFields[key]));
    if (field.tag === 'TRecord') return field;
    if (field.tag === 'TCon' && field.name === T_UNION) {
      const records = field.args
        .map(a => engine.maybeExpandAlias(engine.subst.apply(a)))
        .filter(a => a.tag === 'TRecord');
      if (records.length === 1) return records[0];
    }
    return undefined;
  };
  const fields: Record<string, Type> = {};
  const labelFields: Array<{ label: import('../hm/types').TLabel; type: Type }> = [];
  // Open rows contributed by spreading open records (`{...a}`, `{a}`) or
  // pre-existing Merge markers.  Preserving them keeps a spread of open
  // records OPEN — `{ ...x, ...y }` where x,y are `{...a}`/`{...b}` becomes
  // `Merge a b` (matching the annotation `{ ...a, ...b }`) instead of
  // collapsing to a closed `{}`.
  const openRows: Array<TVar | import('../hm/types').TRow> = [];
  let hiddenFields: Set<string> | undefined;
  const mergeField = (k: string, incoming: Type): void => {
    const prior = fields[k];
    if (prior) {
      const stripped = stripUndefinedFromUnion(incoming);
      if (stripped !== incoming) {
        fields[k] = stripped;
        return;
      }
      const priorR = engine.subst.apply(prior);
      const incomingR = engine.subst.apply(incoming);
      fields[k] = deepMergeTypes(priorR, incomingR);
      return;
    }
    fields[k] = incoming;
  };
  // Absorb one spread source into fields / labelFields / openRows.
  const absorbSpread = (part: Type): void => {
    if (part.tag === 'TRecord') {
      // Special case: prior concrete field + incoming `T | Undefined` (the
      // "key may be missing" marker) — an absent key is not copied by spread,
      // so the prior value wins.  Handled inside mergeField via stripUndefined.
      for (const k in part.fields) mergeField(k, part.fields[k]);
      if (part.labelFields) for (const lf of part.labelFields) labelFields.push(lf);
      if (part.rest) openRows.push(part.rest);
      return;
    }
    if (part.tag === 'TCon' && part.name === T_MERGE) {
      for (const arg of part.args) absorbSpread(engine.subst.apply(arg));
      return;
    }
    if (part.tag === 'TRow' || part.tag === 'TVar') {
      openRows.push(part);
    }
  };
  // A copy of one value (`{ ...props }`, a JSX `<Comp {...props} />`) has the
  // type of that value, also when it is a type variable (`props :: p`);
  // absorbing it into a record lost it (`{}`).
  if (node.properties.length === 1 && node.properties[0].type === 'SpreadElement') {
    const only = engine.subst.apply(inferExpression(engine, node.properties[0].argument, env));
    if (only.tag !== 'TRecord' && !(only.tag === 'TCon' && only.name === T_MERGE)) {
      engine.recordNodeType(node, only);
      return only;
    }
  }
  for (const prop of node.properties) {
    if (prop.type === 'SpreadElement') {
      // Spread in object: { ...obj, x: 1 }
      const spreadType = inferExpression(engine, prop.argument, env);
      const resolved = engine.subst.apply(spreadType);
      // Only records (closed or open) and Merge markers contribute structure;
      // a bare spread of an unknown type variable is left untouched, matching
      // the previous behaviour.
      if (resolved.tag === 'TRecord' || (resolved.tag === 'TCon' && resolved.name === T_MERGE)) {
        absorbSpread(resolved);
      }
      continue;
    }
    if (prop.type === 'Property') {
      let keyName: string | null = null;
      if (prop.key.type === 'Literal') {
        keyName = String(prop.key.value);
      } else if (prop.key.type === 'Identifier' && !prop.computed) {
        keyName = prop.key.name;
      }
      // Computed key `{ [expr]: value }`: the key is the VALUE of `expr`.  A
      // literal type names the field, a label variable makes a label field,
      // anything else is a key known only at runtime (a fresh label: the
      // record is a dictionary for it).
      if (prop.computed && !keyName) {
        const keyType = engine.subst.apply(inferExpression(engine, prop.key, env));
        const literal = keyType.tag === 'TLabel' && keyType.kind === 'lit'
          ? keyType.value
          : keyType.tag === 'TCon' && keyType.stringLiteral !== undefined ? keyType.stringLiteral : null;
        if (literal !== null) {
          keyName = literal;
        } else if (node.properties.length === 1 && (keyType.tag === 'TVar'
            || (keyType.tag === 'TCon' && keyType.args.length === 0
              && (keyType.name === 'String' || keyType.name === 'Number')))) {
          // The usual form, `{ [key]: value }` with a runtime key (a String, a
          // Number, or a key of a type not known yet): a dictionary, which
          // `Object.assign` and spreads merge as such.
          const valueType = inferExpression(engine, prop.value, env);
          const dict = tCon('Object', [tCon('String'), valueType]);
          engine.recordNodeType(prop, valueType);
          engine.recordNodeType(node, dict);
          return dict;
        } else {
          const valueType = inferExpression(engine, prop.value, env);
          const label = keyType.tag === 'TLabel' ? keyType : tLabelVar();
          labelFields.push({ label, type: valueType });
          engine.recordNodeType(prop, valueType);
          continue;
        }
      }
      if (prop.computed && !keyName) {
        inferExpression(engine, prop.key, env);
        inferExpression(engine, prop.value, env);
        continue;
      }
      if (keyName) {
        const expectedField = expectedRecord && expectedRecord.tag === 'TRecord'
          ? expectedRecord.fields[keyName] && engine.subst.apply(expectedRecord.fields[keyName])
          : undefined;
        if (expectedField && expectedField.tag === 'TForall') {
          // Polymorphic field: check the value against the skolemized body
          // and keep the quantifier on the field so the record still matches
          // the annotation.
          engine.inferRankNArgument(prop.value, env, expectedField, new Set());
          fields[keyName] = expectedField;
          engine.recordNodeType(prop, expectedField);
          continue;
        }
        const isFunctionLiteral = prop.value.type === 'ArrowFunctionExpression' || prop.value.type === 'FunctionExpression';
        const functionField = isFunctionLiteral ? expectedFunctionField(keyName) : undefined;
        const isStringLiteral = isStringLiteralChoice(prop.value as AstNode);
        const literalField = isStringLiteral ? expectedLiteralField(keyName) : undefined;
        const recordField = prop.value.type === 'ObjectExpression' ? expectedRecordField(keyName) : undefined;
        const valueType = functionField
          ? engine.inferExpressionWithExpected(prop.value, env, functionField)
          : literalField
            ? (prop.value.type === 'Literal'
              ? inferLiteral(engine, prop.value as estree.Literal, literalField)
              : engine.inferExpressionWithExpected(prop.value, env, literalField))
            : recordField
              ? engine.inferExpressionWithExpected(prop.value, env, recordField)
              : inferExpression(engine, prop.value, env);
        if (literalField) engine.recordNodeType(prop.value, valueType);
        // Standalone `// ::hidden` directive above this property: still
        // include the field in the record so structural unification at
        // call sites accepts callers that require it, but record the name
        // in `hiddenFields` so completion/hover suppress it.
        fields[keyName] = valueType;
        if (isHiddenPropertyOffset(prop.start)) {
          if (!hiddenFields) hiddenFields = new Set();
          hiddenFields.add(keyName);
        }
        engine.recordNodeType(prop, valueType);
      }
    }
  }
  const hasConcrete = Object.keys(fields).length > 0 || labelFields.length > 0;
  const buildRecord = (rest?: TVar | import('../hm/types').TRow): Type => {
    const out = rest ? tOpenRecord(fields, rest) : tRecord(fields);
    if (labelFields.length > 0) (out as { labelFields?: typeof labelFields }).labelFields = labelFields;
    if (hiddenFields) (out as { hiddenFields?: Set<string> }).hiddenFields = hiddenFields;
    return out;
  };
  let rec: Type;
  if (openRows.length === 0) {
    rec = buildRecord();
  } else if (openRows.length === 1) {
    rec = buildRecord(openRows[0]);
  } else {
    // Two or more open rows: mirror the annotation parser's lowering of
    // `{ ...a, ...b }` to `Merge a b` so the body type matches the
    // declared return type.  A leading concrete record carries any
    // fixed fields/labels.
    const args: Type[] = [];
    if (hasConcrete) args.push(buildRecord());
    for (const r of openRows) args.push(r);
    rec = tCon(T_MERGE, args);
  }
  return rec;
}

// --- Constraint-method dispatch moved to ./expr-constraint-lookup ---
export {
  resolveKvConstraintNames,
  collectAllKvConstraintNames,
  lookupConstraintMethod,
} from './expr-constraint-lookup';

// --- Prototype method assignment moved to ./expr-prototype ---
export { tryInferPrototypeMethodAssignment } from './expr-prototype';

// --- Function-expression inference moved to ./expr-functions ---
export {
  inferFunctionExpression,
  bindFunctionParams,
  tryDetectConditionalReturn,
  checkUnionVsExpected,
  inferBlockReturnType,
  collectAllReturnTypes,
} from './expr-functions';

// --- Assignment-expression inference moved to ./expr-assignment ---
export { inferAssignmentExpression, trackModuleExports } from './expr-assignment';

// --- Member-expression inference moved to ./expr-member ---
export {
  inferMemberExpression,
  builtinConstructorType,
  OBJECT_PROTOTYPE_METHOD_NAMES,
  objectPrototypeMethodType,
} from './expr-member';

/**
 * Type of a `require ("specifier")` expression: the module's runtime value.
 * CommonJS `module.exports = X` modules expose that value as their `default`
 * export; otherwise the value is the record of all named exports.  An untyped
 * module yields the opaque `Any`; an unresolvable specifier reports
 * "Cannot resolve module" on the specifier (and yields `Any` so the error
 * does not cascade into unrelated "unbound" diagnostics).
 */
function inferRequireExpression(engine: InferenceEngine, node: estree.CallExpression): Type {
  const arg = node.arguments[0] as estree.Literal;
  const specifier = arg.value as string;
  engine.recordNodeType(node.callee as AstNode, tAnyType);
  if (!engine.importResolver) return tAnyType;
  const resolved = engine.importResolver(specifier);
  if (!resolved) {
    engine.addDiag(`Cannot resolve module '${specifier}'`, arg as AstNode);
    return tAnyType;
  }
  if (isUntypedModule(resolved)) return tAnyType;
  const def = resolved.get('default');
  return def ? instantiate(def) : exportsToRecord(resolved);
}

/**
 * Environment for the right operand of `left && right`: what `left` being
 * truthy proves.  A bare identifier, a `typeof x === "…"` test and a
 * `::narrow` predicate call narrow; a nested `a && b` narrows by both
 * (`typeof x === "number" && Math.floor (x) === x && x >= MIN`).  Other
 * tests (`x !== null`, member checks) are left alone here.
 */
function narrowForAndRight(engine: InferenceEngine, left: AstNode, env: TypeEnv): TypeEnv {
  if (left.type === 'LogicalExpression' && (left as estree.LogicalExpression).operator === '&&') {
    const l = left as estree.LogicalExpression;
    return narrowForAndRight(engine, l.right as AstNode, narrowForAndRight(engine, l.left as AstNode, env));
  }
  if (left.type === 'Identifier'
      || isNullCheckTest(left)
      || extractTypeofCheck(left)
      || extractTypePredicateNarrowing(engine.subst, left, env)
      || isHasTest(left)) {
    return computeNarrowedEnvs(engine.subst, left, env, engine.annotationMap).consEnv;
  }
  return env;
}

/** `x == null`, `x !== undefined`, `obj.prop != null` … */
function isNullCheckTest(node: AstNode): boolean {
  return extractNullCheck(node) !== null || extractMemberNullCheck(node) !== null;
}

/**
 * The env for the right side of `left || right`: `right` only runs when
 * `left` is falsy.  Null checks narrow (`until == null || until.getTime ()`);
 * other tests leave the env as it is.
 */
function narrowForOrRight(engine: InferenceEngine, left: AstNode, env: TypeEnv): TypeEnv {
  if (left.type === 'LogicalExpression' && (left as estree.LogicalExpression).operator === '||') {
    const l = left as estree.LogicalExpression;
    return narrowForOrRight(engine, l.right as AstNode, narrowForOrRight(engine, l.left as AstNode, env));
  }
  return isNullCheckTest(left) || isHasTest(left)
    ? computeNarrowedEnvs(engine.subst, left, env, engine.annotationMap).altEnv
    : env;
}
