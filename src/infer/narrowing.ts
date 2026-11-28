// ============================================================================
// Narrowing — null/undefined checks, type predicates, conditional returns
//
// Plain language: inside an `if`, the checker can know MORE about a value
// than outside it.  If `x` is `Number | Null` and the code says
// `if (x !== null)`, then inside that branch `x` is just `Number`.  This
// file implements that sharpening ("narrowing") for null/undefined checks,
// `typeof` tests, literal comparisons, and user-declared predicate functions
// (`::narrow` — e.g. `isString(x)` proving `x` is a String).
// ============================================================================

import {
  Type,
  TVar,
  TRecord,
  TLabel,
  tFun,
  tCon,
  tUnion,
  tVar,
  typeToString,
  mono,
  tNumber,
  tString,
  tBool,
  tBigInt,
  tSymbol,
  tAnyFunction,
  tAnyObject,
  AstNode,
  T_UNION,
  T_FUNCTION,
  T_OBJECT,
  T_ARRAY,
  parseKvName,
  isUnion,
} from '../hm/types';
import { Substitution } from '../hm/substitution';
import * as walk from '../walking';
import type * as estree from '../estree';
import { TypeEnv, instantiate, generalize } from '../hm/env';
import { TypeAnnotation } from '../commentParser';
import { getDataType, getParentTypeName } from '../registries/dataTypeRegistry';
import { getTypeArity, lookupMethod } from '../registries/methodRegistry';
import { structuralEquals} from '../hm/typeUtils';
import { unify, UnificationError } from '../hm/unify';
import { variantThisScheme } from './helpers';

// ---------------------------------------------------------------------------
// Union helpers
// ---------------------------------------------------------------------------

/** The members of a union, nested unions flattened (`Null | (String | Null)`
 *  — e.g. a ternary `c ? null : f (x)` with `f :: a -> String | Null` — has
 *  the members Null, String, Null). */
function unionMembers(t: Type): Type[] {
  return isUnion(t) ? t.args.flatMap(unionMembers) : [t];
}

/** Filter union members (nested unions flattened) and unwrap single-element
 *  results. */
export function filterUnion(union: Type, predicate: (t: Type) => boolean): Type {
  const filtered = isUnion(union)
    ? unionMembers(union).filter(predicate)
    : [union];
  if (filtered.length === 0) return union;
  if (filtered.length === 1) return filtered[0];
  return tUnion(filtered);
}

// ---------------------------------------------------------------------------
// Pure AST / type helpers (no engine state)
// ---------------------------------------------------------------------------

/** Check if a block (or single statement) always reaches a return or throw. */
export function blockAlwaysReturns(node: AstNode): boolean {
  if (node.type === 'ReturnStatement' || node.type === 'ThrowStatement') return true;
  if (node.type === 'BlockStatement') {
    for (const stmt of (node.body ?? [])) {
      if (blockAlwaysReturns(stmt)) return true;
    }
  }
  return false;
}

/**
 * Return true if an AST literal or identifier evaluates to a truthy value.
 *
 * Handles Literal nodes (numbers, strings, booleans, null) and Identifier
 * nodes. Falsy identifiers ('false', 'undefined', 'NaN') and unknown
 * identifiers return false via the default fallback path.
 */
export function isLiteralTruthy(arg: AstNode): boolean {
  if (arg.type === 'Literal') {
    const val = arg.value;
    if (val === null || val === 0 || val === '' || val === false) return false;
    return val !== undefined;
  }
  if (arg.type === 'Identifier') {
    if (arg.name === 'true') return true;
    // 'false', 'undefined', 'NaN' and other identifiers are not truthy literals
    return false;
  }
  return false;
}

/**
 * Remove Null and Undefined from a union type.
 * If the type is not a union, return it unchanged.
 * If removing leaves a single type, unwrap the union.
 */
export function removeNullUndefined(t: Type): Type {
  return filterUnion(t, arg =>
    !(arg.tag === 'TCon' && (arg.name === 'Null' || arg.name === 'Undefined'))
  );
}

/**
 * Check if a type accepts Undefined — either IS Undefined or is a Union containing Undefined.
 */
export function typeAcceptsUndefined(subst: Substitution, t: Type): boolean {
  const resolved = subst.apply(t);
  if (resolved.tag === 'TCon' && resolved.name === 'Undefined') return true;
  if (isUnion(resolved)) {
    return resolved.args.some(a => a.tag === 'TCon' && a.name === 'Undefined');
  }
  return false;
}

// ---------------------------------------------------------------------------
// Null check extraction
// ---------------------------------------------------------------------------

/**
 * Extract null/undefined check info from a condition expression.
 * Recognizes patterns:
 *   x == null, x === null, x == undefined, x === undefined
 *   x != null, x !== null, x != undefined, x !== undefined
 *   typeof x === 'undefined', typeof x !== 'undefined'
 *
 * Returns { varName, isNullCheckPositive } where isNullCheckPositive=true
 * means the condition CHECKS for null (e.g. x == null), and false means
 * the condition REJECTS null (e.g. x != null).
 */
/** Check if a node represents `null` or `undefined`. */
function isNullOrUndefined(n: AstNode): boolean {
  return (n.type === 'Literal' && n.value === null) ||
    (n.type === 'Identifier' && n.name === 'undefined');
}

/**
 * Recognise an equality/inequality binary operator and return the polarity
 * (positive for `==` / `===`, negative for `!=` / `!==`) or `null` if `op`
 * is not a comparison.
 */
function eqOpPolarity(op: string): boolean | null {
  switch (op) {
    case '==':
    case '===': return true;
    case '!=':
    case '!==': return false;
    default:    return null;
  }
}

/**
 * For a binary equality node, try matching `(operandA, operandB)` and then
 * the reverse `(operandB, operandA)` so callers only need a single matcher.
 */
function matchOperandPair<T>(
  node: AstNode,
  fn: (a: AstNode, b: AstNode) => T | null,
): T | null {
  if (node.type !== 'BinaryExpression') return null;
  return fn(node.left, node.right) ?? fn(node.right, node.left);
}

export function extractNullCheck(node: AstNode): { varName: string; isNullCheckPositive: boolean } | null {
  const isPositive = node.type === 'BinaryExpression'
    ? eqOpPolarity(node.operator as string)
    : null;
  if (isPositive === null) return null;

  return matchOperandPair(node, (ident, nullish) => {
    // Pattern: x == null / x === undefined
    if (ident.type === 'Identifier' && isNullOrUndefined(nullish)) {
      return { varName: ident.name, isNullCheckPositive: isPositive };
    }
    // Pattern: typeof x === 'undefined'
    if (ident.type === 'UnaryExpression' && ident.operator === 'typeof' &&
        ident.argument?.type === 'Identifier' &&
        nullish.type === 'Literal' && nullish.value === 'undefined') {
      return { varName: ident.argument.name, isNullCheckPositive: isPositive };
    }
    return null;
  });
}

/**
 * `obj.prop == null`, `obj.prop !== undefined`, `obj["prop"] != null`, and
 * deeper paths on an identifier (`cfg.retry.delayMs == null`).  `path` is
 * the chain of field names from `objName`; `propName` is its last field.
 * Same polarity as {@link extractNullCheck}.
 */
export function extractMemberNullCheck(
  node: AstNode,
): { objName: string; propName: string; path: string[]; isNullCheckPositive: boolean } | null {
  const isPositive = node.type === 'BinaryExpression'
    ? eqOpPolarity(node.operator as string)
    : null;
  if (isPositive === null) return null;
  return matchOperandPair(node, (member, nullish) => {
    if (member.type !== 'MemberExpression' || !isNullOrUndefined(nullish)) return null;
    const path: string[] = [];
    let cur: AstNode = member;
    while (cur.type === 'MemberExpression') {
      const propName = memberPropName(cur as unknown as estree.MemberExpression);
      if (propName === null) return null;
      path.unshift(propName);
      cur = (cur as unknown as estree.MemberExpression).object as AstNode;
    }
    if (cur.type !== 'Identifier') return null;
    return { objName: cur.name as string, propName: path[path.length - 1], path, isNullCheckPositive: isPositive };
  });
}

/**
 * The env key that marks member `obj.prop` as non-null in a narrowed branch
 * (a `.` never occurs in an identifier, so it cannot collide with a binding).
 * Rebinding `obj` in the branch shadows nothing here: the key names the path,
 * and a plain reassignment of `obj` inside a ternary branch is not modelled.
 */
export function nonNullMemberKey(objName: string, propName: string): string {
  return objName + '.' + propName;
}

/**
 * A value path that can be compared textually: `m`, `this.m`, `state.byTeam`,
 * `row.team_id`, `byKey["x"]`, a string or number literal.  Null otherwise
 * (a call, an index by a variable, …).
 */
function valuePath(node: AstNode | null | undefined): string | null {
  if (!node) return null;
  if (node.type === 'Identifier') return node.name as string;
  if (node.type === 'ThisExpression') return 'this';
  if (node.type === 'Literal') {
    const v = (node as unknown as estree.Literal).value;
    return typeof v === 'string' || typeof v === 'number' ? JSON.stringify(v) : null;
  }
  if (node.type === 'MemberExpression') {
    const m = node as unknown as estree.MemberExpression;
    const obj = valuePath(m.object as AstNode);
    if (obj === null) return null;
    if (!m.computed && m.property?.type === 'Identifier') return obj + '.' + (m.property.name as string);
    const key = m.computed ? valuePath(m.property as AstNode) : null;
    return key !== null && (m.property as AstNode).type === 'Literal' ? obj + '[' + key + ']' : null;
  }
  return null;
}

/**
 * Env key marking that `map` has `key` (after `map.has (key)`): a later
 * `map.get (key)` on the same paths cannot miss (see `expr-member` call
 * handling in `calls.ts`).  Null when either side is not a plain path.
 */
export function presentKeyMarker(map: AstNode, key: AstNode): string | null {
  const m = valuePath(map);
  const k = valuePath(key);
  return m === null || k === null ? null : '\u0000has:' + m + '|' + k;
}

/** `X.<method> (K)` with one argument: the receiver and key nodes. */
function methodCallOf(node: AstNode | null | undefined, method: string): { map: AstNode; key: AstNode } | null {
  if (!node || node.type !== 'CallExpression') return null;
  const call = node as unknown as estree.CallExpression;
  const callee = call.callee as AstNode;
  if (callee.type !== 'MemberExpression') return null;
  const m = callee as unknown as estree.MemberExpression;
  if (m.computed || m.property?.type !== 'Identifier' || m.property.name !== method) return null;
  const arity = method === 'set' ? 2 : 1;
  if (call.arguments.length !== arity || call.arguments[0].type === 'SpreadElement') return null;
  return { map: m.object as AstNode, key: call.arguments[0] as AstNode };
}

/** Is this a (possibly negated) `m.has (k)` test on plain paths? */
export function isHasTest(node: AstNode): boolean {
  let target = node;
  while (target.type === 'UnaryExpression' && (target as unknown as estree.UnaryExpression).operator === '!') {
    target = (target as unknown as estree.UnaryExpression).argument as AstNode;
  }
  const has = methodCallOf(target, 'has');
  return !!has && presentKeyMarker(has.map, has.key) !== null;
}

/** The marker of `map.get (key)` when this call is one, else null. */
export function getCallMarker(node: AstNode): string | null {
  const g = methodCallOf(node, 'get');
  return g ? presentKeyMarker(g.map, g.key) : null;
}

/** Does this statement always leave the enclosing block (return, throw,
 *  continue, break — directly or as the last statement of a block)? */
export function leavesBlock(node: AstNode): boolean {
  if (['ReturnStatement', 'ThrowStatement', 'ContinueStatement', 'BreakStatement'].includes(node.type)) return true;
  if (node.type === 'BlockStatement') {
    const body = (node as unknown as estree.BlockStatement).body as AstNode[];
    return body.length > 0 && leavesBlock(body[body.length - 1]);
  }
  return false;
}

/**
 * The key that is present after this statement, as an env marker:
 * `if (!m.has (k)) m.set (k, …);` (the branch adds it) or
 * `if (!m.has (k)) return …;` (the rest only runs when it is there).  An
 * `else` changes nothing: it runs when the key was already there.
 */
export function keyPresentAfter(stmt: AstNode): string | null {
  if (stmt.type !== 'IfStatement') return null;
  const ifs = stmt as unknown as estree.IfStatement;
  const test = ifs.test as AstNode;
  if (test.type !== 'UnaryExpression' || (test as unknown as estree.UnaryExpression).operator !== '!') return null;
  const has = methodCallOf((test as unknown as estree.UnaryExpression).argument as AstNode, 'has');
  if (!has) return null;
  const marker = presentKeyMarker(has.map, has.key);
  if (marker === null) return null;
  const cons = ifs.consequent as AstNode;
  if (leavesBlock(cons)) return marker;
  const stmts = cons.type === 'BlockStatement' ? (cons as unknown as estree.BlockStatement).body as AstNode[] : [cons];
  const adds = stmts.some(st => {
    if (st.type !== 'ExpressionStatement') return false;
    const set = methodCallOf((st as unknown as estree.ExpressionStatement).expression as AstNode, 'set');
    return !!set && presentKeyMarker(set.map, set.key) === marker;
  });
  return adds ? marker : null;
}

/** The property name of `obj.prop` or `obj["prop"]`, else null. */
function memberPropName(member: estree.MemberExpression): string | null {
  if (!member.computed && member.property?.type === 'Identifier') return member.property.name as string;
  if (member.computed && member.property?.type === 'Literal'
      && typeof (member.property as estree.Literal).value === 'string') {
    return (member.property as estree.Literal).value as string;
  }
  return null;
}

/**
 * The record type of `objName` with Null/Undefined removed from the field at
 * `path` (`["retry", "delayMs"]`: every record on the way is rebuilt), or
 * null when the path does not run through records to a nullable field.
 */
function recordWithNonNullField(subst: Substitution, env: TypeEnv, objName: string, path: string[]): Type | null {
  const objScheme = env.lookup(objName);
  if (!objScheme) return null;
  return recordWithNonNullPath(subst, subst.apply(objScheme.type), path);
}

function recordWithNonNullPath(subst: Substitution, obj: Type, path: string[]): Type | null {
  const [propName, ...rest] = path;
  if (obj.tag !== 'TRecord' || !Object.prototype.hasOwnProperty.call(obj.fields, propName)) return null;
  const field = subst.apply(obj.fields[propName]);
  const narrowed = rest.length === 0 ? removeNullUndefined(field) : recordWithNonNullPath(subst, field, rest);
  if (narrowed === null || structuralEquals(narrowed, field)) return null;
  return { ...obj, fields: { ...obj.fields, [propName]: narrowed } };
}

// ---------------------------------------------------------------------------
// typeof narrowing
// ---------------------------------------------------------------------------

/**
 * Map a `typeof` string literal to the corresponding HM type.
 * `'undefined'` is intentionally absent here — it is handled by
 * `extractNullCheck` because it represents a null/undefined narrowing.
 */
function typeofStringToType(s: string): Type | null {
  switch (s) {
    case 'string':    return tString;
    case 'number':    return tNumber;
    case 'boolean':   return tBool;
    case 'bigint':    return tBigInt;
    case 'symbol':    return tSymbol;
    case 'function':  return tAnyFunction();
    case 'object':    return tAnyObject();
    // 'undefined' is handled by extractNullCheck — not here
    default:          return null;
  }
}

/**
 * Whether a union member `t` belongs to the typeof category described by
 * `narrowedTo`.  For `typeof x === "function"` / `"object"` the narrowed type
 * is *any* function / object (`Function [a] b` / `Object k a`), so a member is
 * part of that category whenever its head constructor name matches — regardless
 * of the applied children's type variables.  Other categories (String, Number,
 * …) fall back to exact structural equality.
 */
export function typeofCategoryMatches(t: Type, narrowedTo: Type): boolean {
  if (structuralEquals(t, narrowedTo)) return true;
  if (t.tag === 'TCon' && narrowedTo.tag === 'TCon' && t.name === narrowedTo.name &&
      (narrowedTo.name === T_FUNCTION || narrowedTo.name === T_OBJECT)) return true;
  return false;
}

/**
 * Extract typeof-based type narrowing from a condition expression.
 * Recognizes:
 *   typeof x === "string"   → { varName: 'x', narrowedType: String, isPositive: true }
 *   typeof x !== "number"   → { varName: 'x', narrowedType: Number, isPositive: false }
 *   "string" === typeof x   → same (reversed operand order)
 *
 * Does NOT handle `typeof x === 'undefined'` — that is a null check
 * (handled by `extractNullCheck`).
 */
export function extractTypeofCheck(node: AstNode): {
  varName: string;
  narrowedType: Type;
  isPositive: boolean;
} | null {
  const isPositive = node.type === 'BinaryExpression'
    ? eqOpPolarity(node.operator as string)
    : null;
  if (isPositive === null) return null;

  return matchOperandPair(node, (typeofExpr, literal) => {
    if (typeofExpr.type !== 'UnaryExpression' || typeofExpr.operator !== 'typeof') return null;
    if (typeofExpr.argument?.type !== 'Identifier') return null;
    if (literal.type !== 'Literal' || typeof literal.value !== 'string') return null;
    if (literal.value === 'undefined') return null; // handled by extractNullCheck
    const narrowedType = typeofStringToType(literal.value as string);
    if (!narrowedType) return null;
    return { varName: typeofExpr.argument.name, narrowedType, isPositive };
  });
}

// ---------------------------------------------------------------------------
// Type predicate narrowing
// ---------------------------------------------------------------------------

/**
 * Find the parameter index for a type predicate's paramName in a function type.
 * For `a -> b -> Boolean` with paramName 'a': returns 0
 * For `(a, b) -> Boolean` with paramName 'b': returns 1
 *
 * @deprecated The narrowed parameter index is now stored directly on the
 * `TypePredicate` (`paramIndex`).  Retained for backward compatibility.
 */
export function findPredicateParamIndex(type: Type, paramName: string): number {
  if (type.tag !== 'TFun') return -1;

  const param = type.param;

  // Single param — commentParser guarantees param is a TVar matching paramName
  if (param.tag === 'TVar' && param.name === paramName) return 0;

  return -1;
}

/**
 * Flatten a (possibly curried) call expression into its base callee and the
 * full, in-order list of argument nodes.  Handles both flat calls
 * (`isString(x)` → callee `isString`, args `[x]`) and curried calls
 * (`hasPropAlt("length")(foldable)` → callee `hasPropAlt`,
 * args `["length", foldable]`).
 */
function flattenCurriedCall(node: AstNode): { callee: AstNode; args: AstNode[] } | null {
  if (node.type !== 'CallExpression') return null;
  const argLists: AstNode[][] = [];
  let cur: AstNode = node;
  while (cur.type === 'CallExpression') {
    argLists.unshift((cur.arguments ?? []) as AstNode[]);
    cur = cur.callee as AstNode;
  }
  return { callee: cur, args: argLists.flat() };
}

/**
 * `::narrow <Variant>` predicate applied to a value whose type is the
 * variant's parent sumtype.  Uses the same phantom-slot schemes as the
 * member form (`variantThisScheme`).  Returns null when not applicable.
 */
function narrowPredicateToVariant(
  subst: Substitution,
  predicate: { varName: string; narrowedType: Type },
  consEnv: TypeEnv,
  altEnv: TypeEnv,
): { consEnv: TypeEnv; altEnv: TypeEnv } | null {
  const target = predicate.narrowedType;
  if (target.tag !== 'TCon') return null;
  const parentName = getParentTypeName(target.name);
  if (!parentName) return null;
  const existing = consEnv.lookup(predicate.varName);
  if (!existing) return null;
  const resolved = subst.apply(existing.type);
  if (resolved.tag !== 'TCon' || resolved.name !== parentName) return null;
  const dt = getDataType(parentName);
  if (!dt) return null;
  const cons = variantThisScheme(target.name, resolved);
  const others = [...dt.variantMap.keys()].filter(v => v !== target.name);
  const alt = others.length === 1 ? variantThisScheme(others[0], resolved) : null;
  return {
    consEnv: cons ? consEnv.extend(predicate.varName, cons) : consEnv,
    altEnv: alt ? altEnv.extend(predicate.varName, alt) : altEnv,
  };
}

/**
 * Extract type predicate narrowing info from a condition expression.
 * Recognizes: if (isString(x)) where isString has annotation
 * `::narrow String` + `a -> Boolean`, as well as multi-parameter / curried
 * predicates such as `if (hasPropAlt("length")(foldable))` where `hasPropAlt`
 * has `::narrow { [k] :: a }` + `k -> { [k] :: a | Undefined } -> Boolean`.
 *
 * Returns { varName, narrowedType, unionRemainder } where:
 * - varName: the identifier being narrowed
 * - narrowedType: the type to narrow to in the true branch
 * - unionRemainder: the remaining union type for the false branch (if applicable)
 */
export function extractTypePredicateNarrowing(
  subst: Substitution,
  node: AstNode,
  env: TypeEnv,
): { varName: string; narrowedType: Type; unionRemainder: Type | null } | null {
  // Support both flat and curried calls; collect the base callee + flat args.
  const flat = flattenCurriedCall(node);
  if (!flat) return null;

  if (flat.callee.type !== 'Identifier') return null;
  const calleeName = flat.callee.name as string;

  // Look up the callee's scheme in the environment
  const calleeScheme = env.lookup(calleeName);
  if (!calleeScheme?.typePredicate) return null;

  const predicate = calleeScheme.typePredicate;

  // The narrowed parameter index is recorded on the predicate (the last
  // curried parameter before the Boolean result).
  const paramIndex = predicate.paramIndex;
  if (paramIndex < 0 || paramIndex >= flat.args.length) return null;

  const arg = flat.args[paramIndex];
  if (arg.type !== 'Identifier') return null;

  const varName = arg.name as string;

  // When the narrowed type references a polymorphic label `[k]`, substitute it
  // with the concrete key argument (e.g. `"length"`) supplied at the linked
  // parameter index, turning `{ [k] :: a }` into `{ length :: a }` so a member
  // access like `foldable.length` resolves in the true branch.
  let narrowedType = predicate.narrowedType;
  if (predicate.keyVarName && predicate.keyParamIndex !== undefined
      && predicate.keyParamIndex >= 0 && predicate.keyParamIndex < flat.args.length) {
    const keyArg = flat.args[predicate.keyParamIndex];
    if (keyArg.type === 'Literal' && typeof (keyArg as estree.Literal).value === 'string') {
      narrowedType = substituteKeyLabel(
        narrowedType, predicate.keyVarName, (keyArg as estree.Literal).value as string,
      );
    }
  }

  // A bare reference to a parametric constructor (e.g. `::narrow Array`) denotes
  // an INSTANCE of that type — saturate it with fresh parameter variables so a
  // narrowed value becomes `Array <fresh>` rather than the (uninhabited)
  // nullary constructor.
  narrowedType = saturateNarrowTargetToInstance(narrowedType);

  // Check current type of the variable for union remainder computation
  const varScheme = env.lookup(varName);
  let unionRemainder: Type | null = null;
  if (varScheme) {
    const resolvedType = subst.apply(varScheme.type);
    if (isUnion(resolvedType)) {
      // When narrowing to a constructor instance (e.g. `Array a`), the fresh
      // saturation vars never match a union member's vars by id, so filter the
      // remainder by the HEAD constructor name instead of structural equality.
      // A union target (`::narrow Null | Undefined`) removes each of its
      // members; matching on the union's own head (`Union`) removed nothing.
      const targets = isUnion(narrowedType) ? unionMembers(narrowedType) : [narrowedType];
      const matchesTarget = (a: Type): boolean => targets.some(t =>
        t.tag === 'TCon' ? a.tag === 'TCon' && a.name === t.name : structuralEquals(a, t));
      const remaining = unionMembers(resolvedType).filter(a => !matchesTarget(a));
      if (remaining.length > 0) {
        unionRemainder = remaining.length === 1 ? remaining[0] : tUnion(remaining);
      }
      // With a union target, the true branch is the overlap: `Number | Null`
      // tested by `::narrow Null | Undefined` is `Null`, not `Null | Undefined`.
      if (isUnion(narrowedType)) {
        const overlap = unionMembers(resolvedType).filter(matchesTarget);
        if (overlap.length > 0) narrowedType = overlap.length === 1 ? overlap[0] : tUnion(overlap);
      }
    }
  }

  return { varName, narrowedType, unionRemainder };
}

/**
 * Resolve the type-parameter arity of a `::narrow` target constructor.
 * Sumtype declarations carry their arity directly; built-in / registered
 * constructors (Array, …) come from the method registry.  Returns 0 when the
 * name is not a parametric constructor.
 */
function narrowTargetArity(name: string): number {
  const dt = getDataType(name);
  if (dt && dt.decl.typeVars.length > 0) return dt.decl.typeVars.length;
  return getTypeArity(name);
}

/**
 * Saturate bare references to parametric constructors with fresh type variables
 * so a `::narrow <Type>` directive denotes an INSTANCE of that type.  A bare
 * `Array` (arity 1) becomes `Array <fresh>`; an already-applied `Array a`,
 * a record, or a ground type is returned unchanged.  Descends into constructor
 * arguments, function parameters/results, and record field types.  Never
 * mutates the input.
 */
function saturateNarrowTargetToInstance(t: Type): Type {
  switch (t.tag) {
    case 'TCon': {
      if (t.args.length === 0) {
        const arity = narrowTargetArity(t.name);
        if (arity > 0) {
          const args: Type[] = [];
          for (let i = 0; i < arity; i++) args.push(tVar());
          return { ...t, args };
        }
        return t;
      }
      return { ...t, args: t.args.map(saturateNarrowTargetToInstance) };
    }
    case 'TFun':
      return {
        ...t,
        param: saturateNarrowTargetToInstance(t.param),
        result: saturateNarrowTargetToInstance(t.result),
      };
    case 'TRecord': {
      const fields: Record<string, Type> = {};
      for (const [k, v] of Object.entries(t.fields)) {
        fields[k] = saturateNarrowTargetToInstance(v);
      }
      const out: TRecord = { ...t, fields };
      if (t.labelFields) {
        out.labelFields = t.labelFields.map(lf => ({
          label: lf.label,
          type: saturateNarrowTargetToInstance(lf.type),
        }));
      }
      return out;
    }
    default:
      return t;
  }
}

/**
 * Replace a polymorphic record label variable (e.g. `[k]`) with a concrete
 * literal label throughout a type.  The matching `labelFields` entry migrates
 * into the record's string-keyed `fields` (e.g. `{ [k] :: a }` with k="length"
 * becomes `{ length :: a }`).
 */
function substituteKeyLabel(t: Type, varName: string, literal: string): Type {
  if (t.tag === 'TRecord') {
    const newFields: Record<string, Type> = { ...t.fields };
    const remainingLabelFields: Array<{ label: TLabel; type: Type }> = [];
    for (const lf of t.labelFields ?? []) {
      const innerType = substituteKeyLabel(lf.type, varName, literal);
      if (lf.label.tag === 'TLabel' && lf.label.kind === 'var' && lf.label.name === varName) {
        newFields[literal] = innerType;
      } else {
        remainingLabelFields.push({ label: lf.label, type: innerType });
      }
    }
    const out: TRecord = { ...t, fields: newFields };
    if (remainingLabelFields.length > 0) out.labelFields = remainingLabelFields;
    else delete out.labelFields;
    return out;
  }
  if (t.tag === 'TCon') {
    return { ...t, args: t.args.map(a => substituteKeyLabel(a, varName, literal)) };
  }
  if (t.tag === 'TFun') {
    return {
      ...t,
      param: substituteKeyLabel(t.param, varName, literal),
      result: substituteKeyLabel(t.result, varName, literal),
    };
  }
  return t;
}

// ---------------------------------------------------------------------------
// OR-predicate collection for union narrowing
// ---------------------------------------------------------------------------

/**
 * Recursively collect type-predicate narrowing info from a LogicalExpression
 * with `||` operator.  E.g. `isPerson(x) || isString(x)` returns two entries.
 * Only collects when ALL leaves are type-predicate calls on the same variable.
 */
function collectOrPredicates(
  subst: Substitution,
  node: AstNode,
  env: TypeEnv,
): { varName: string; narrowedType: Type }[] {
  if (node.type === 'LogicalExpression' && node.operator === '||') {
    const left = collectOrPredicates(subst, node.left, env);
    const right = collectOrPredicates(subst, node.right, env);
    if (left.length > 0 && right.length > 0) {
      return [...left, ...right];
    }
    return [];
  }
  const predicate = extractTypePredicateNarrowing(subst, node, env);
  if (predicate) {
    return [{ varName: predicate.varName, narrowedType: predicate.narrowedType }];
  }
  return [];
}

// ---------------------------------------------------------------------------
// ::narrow on member expressions / method calls
// ---------------------------------------------------------------------------

/**
 * Handle `if (f.isLeft)` (getter) and `if (f.isLeft())` (method call)
 * when the annotation has `::narrow`.  Returns narrowed envs or null.
 */
function extractNarrowMemberExpression(
  test: AstNode,
  env: TypeEnv,
  subst: Substitution,
  annotationMap: Map<string, TypeAnnotation> | undefined,
  consEnv: TypeEnv,
  altEnv: TypeEnv,
): { consEnv: TypeEnv; altEnv: TypeEnv } | null {
  if (!annotationMap) return null;

  // Determine the object and property from either:
  //   f.isLeft      (MemberExpression)
  //   f.isLeft()    (CallExpression with MemberExpression callee)
  let varName: string | null = null;
  let propName: string | null = null;

  if (test.type === 'MemberExpression'
      && test.object.type === 'Identifier'
      && test.property.type === 'Identifier') {
    varName = test.object.name as string;
    propName = test.property.name as string;
  } else if (test.type === 'CallExpression'
      && test.callee?.type === 'MemberExpression'
      && test.callee.object?.type === 'Identifier'
      && test.callee.property?.type === 'Identifier') {
    varName = test.callee.object.name as string;
    propName = test.callee.property.name as string;
  }

  if (!varName || !propName) return null;

  const varScheme = env.lookup(varName);
  if (!varScheme) return null;

  const resolvedType = subst.apply(varScheme.type);
  if (resolvedType.tag !== 'TCon') return null;

  const narrowKey = `${resolvedType.name}#${propName}`;
  const local = annotationMap.get(narrowKey);
  const ann = local?.narrowVariant ? local : lookupMethod(resolvedType.name, propName)?.narrowAnnotation;
  if (!ann?.narrowVariant) return null;

  // Only narrow when the call pattern matches the annotation type:
  //   f.isLeft   (MemberExpression) → annotation must be a getter (~> Boolean)
  //   f.isLeft() (CallExpression)   → annotation must be a method (~> () -> Boolean)
  const isCall = test.type === 'CallExpression';
  const isMethod = ann.methodType?.tag === 'TFun';
  if (isCall !== isMethod) return null;

  const parentName = resolvedType.name;
  const dt = getDataType(parentName);
  if (!dt || !dt.variantMap.has(ann.narrowVariant)) return null;

  consEnv = consEnv.extend(`__sumtypeVariant_${varName}`, mono(tCon(ann.narrowVariant, [])));
  // Rebind `varName` itself to a Scheme that quantifies the variant's
  // phantom type parameters. Each lookup of the narrowed variable then
  // freshens those positions, so e.g. `return f` (with f narrowed to Left,
  // whose `a` slot is phantom) unifies with the expected `Either e b`
  // instead of producing an infinite-type / spurious union mismatch.
  const consPhantomScheme = variantThisScheme(ann.narrowVariant, resolvedType);
  if (consPhantomScheme) {
    consEnv = consEnv.extend(varName, consPhantomScheme);
  }
  // For alt branch: intersect remaining variants with any existing narrowing
  let candidateVariants = [...dt.variantMap.keys()].filter(v => v !== ann.narrowVariant);
  const existingScheme = env.lookup(`__sumtypeVariant_${varName}`);

  if (existingScheme) {
    const existingType = subst.apply(existingScheme.type);
    const existingNames = new Set<string>();
    if (existingType.tag === 'TCon') {
      if (existingType.name === T_UNION) {
        for (const m of existingType.args) {
          if (m.tag === 'TCon') existingNames.add(m.name);
        }
      } else {
        existingNames.add(existingType.name);
      }
    }
    if (existingNames.size > 0) {
      candidateVariants = candidateVariants.filter(v => existingNames.has(v));
    }
  }
  if (candidateVariants.length === 1) {
    altEnv = altEnv.extend(`__sumtypeVariant_${varName}`, mono(tCon(candidateVariants[0], [])));
    const altPhantomScheme = variantThisScheme(candidateVariants[0], resolvedType);
    if (altPhantomScheme) {
      altEnv = altEnv.extend(varName, altPhantomScheme);
    }
  } else if (candidateVariants.length > 1) {
    altEnv = altEnv.extend(`__sumtypeVariant_${varName}`, mono(tUnion(candidateVariants.map(v => tCon(v, [])))));
  }
  return { consEnv, altEnv };
}

// ---------------------------------------------------------------------------
// Narrowed environments (if-statement branches)
// ---------------------------------------------------------------------------

/**
 * Compute narrowed environments for the consequent and alternate branches
 * of an if-statement.  Handles null checks, truthiness narrowing, and
 * type-predicate narrowing (e.g. `isString(x)`).
 */
export function computeNarrowedEnvs(
  subst: Substitution,
  test: AstNode,
  env: TypeEnv,
  annotationMap?: Map<string, TypeAnnotation>,
): { consEnv: TypeEnv; altEnv: TypeEnv } {
  let consEnv = env;
  let altEnv = env;

  // 1. Null/undefined equality check: x == null, x !== undefined, etc.
  const nullCheck = extractNullCheck(test);
  if (nullCheck) {
    const varScheme = env.lookup(nullCheck.varName);
    if (varScheme) {
      const resolvedType = subst.apply(varScheme.type);
      const narrowed = removeNullUndefined(resolvedType);
      if (nullCheck.isNullCheckPositive) {
        altEnv = altEnv.extend(nullCheck.varName, mono(narrowed));
      } else {
        consEnv = consEnv.extend(nullCheck.varName, mono(narrowed));
      }
    }
    return { consEnv, altEnv };
  }

  // 1b. Member null check: `q.from == null ? now : q.from` — narrow the
  //     field of a record-typed identifier in the branch where it is set.
  //     When the object is not a record (a built-in or nominal type whose
  //     member comes from the method registry, e.g. an `Error` augmented
  //     with `::global Error#retryAt :: Date | Undefined`), the branch
  //     records the member PATH as non-null instead; member access on that
  //     exact path strips Null/Undefined (see `inferMemberExpression`).
  const memberNullCheck = extractMemberNullCheck(test);
  if (memberNullCheck) {
    const narrowedObj = recordWithNonNullField(subst, env, memberNullCheck.objName, memberNullCheck.path);
    // The path marker (non-record objects) stays one level deep: member
    // access only consults it for `ident.prop`.
    const binding = narrowedObj
      ? { name: memberNullCheck.objName, scheme: mono(narrowedObj) }
      : memberNullCheck.path.length === 1 && env.lookup(memberNullCheck.objName)
        ? { name: nonNullMemberKey(memberNullCheck.objName, memberNullCheck.propName), scheme: mono(tBool) }
        : null;
    if (binding) {
      if (memberNullCheck.isNullCheckPositive) {
        altEnv = altEnv.extend(binding.name, binding.scheme);
      } else {
        consEnv = consEnv.extend(binding.name, binding.scheme);
      }
    }
    return { consEnv, altEnv };
  }

  // 2. typeof check: if (typeof x === "string")
  const typeofCheck = extractTypeofCheck(test);
  if (typeofCheck) {
    const varScheme = env.lookup(typeofCheck.varName);
    if (varScheme) {
      const resolvedType = subst.apply(varScheme.type);
      const narrowedTo = typeofCheck.narrowedType;
      // `typeof x === "function"` / `=== "object"` narrows to *any* function /
      // object, so a union member is part of that category when its head
      // constructor name matches (regardless of the applied children's vars).
      const sameCategory = (t: Type): boolean => typeofCategoryMatches(t, narrowedTo);
      if (typeofCheck.isPositive) {
        // typeof x === "string" → consEnv narrows to String
        consEnv = consEnv.extend(typeofCheck.varName, mono(typeofCheck.narrowedType));
        // altEnv: remove the matched type from unions
        const remainder = filterUnion(resolvedType, t => !sameCategory(t));
        if (!structuralEquals(remainder, resolvedType)) {
          altEnv = altEnv.extend(typeofCheck.varName, mono(remainder));
        }
      } else {
        // typeof x !== "string" → altEnv narrows to String
        altEnv = altEnv.extend(typeofCheck.varName, mono(typeofCheck.narrowedType));
        // consEnv: remove the matched type from unions
        const remainder = filterUnion(resolvedType, t => !sameCategory(t));
        if (!structuralEquals(remainder, resolvedType)) {
          consEnv = consEnv.extend(typeofCheck.varName, mono(remainder));
        }
      }
    }
    return { consEnv, altEnv };
  }

  // 3. Type predicate call: if (isString(x))
  const predicate = extractTypePredicateNarrowing(subst, test, env);
  if (predicate) {
    // A predicate that narrows to a sumtype VARIANT (`::narrow Next` on
    // `isNext`) applied to a value of the parent type (`Step b a`): narrow
    // like the member form `acc.isNext` — the variant in the true branch,
    // the only other variant in the false branch.
    const variantEnvs = narrowPredicateToVariant(subst, predicate, consEnv, altEnv);
    if (variantEnvs) return variantEnvs;
    // Reconcile the narrowed type with the value's CURRENT type so an open
    // record tail (`...r`) absorbs the fields the value already carries: e.g.
    // narrowing `{ length :: Number, name :: String }` with a predicate whose
    // shape is `{ length :: a, ...r }` must keep `name` reachable in the true
    // branch (the `...r` is "substituted" with `{ name :: String }`).  Only do
    // this when the value ALREADY has a concrete record type — for a free /
    // polymorphic value (a generic function parameter) we keep the bare
    // narrowed shape so its fresh field vars stay fully generalizable (each
    // use instantiates a fresh copy, e.g. `return foldable.length` can still
    // satisfy a `-> Number` annotation).  The unification runs in a LOCAL
    // substitution so nothing is pinned globally.
    let narrowed = predicate.narrowedType;
    const existing = consEnv.lookup(predicate.varName);
    if (existing && narrowed.tag === 'TRecord') {
      const existingResolved = subst.apply(existing.type);
      if (existingResolved.tag === 'TRecord') {
        try {
          const s = unify(narrowed, existingResolved);
          narrowed = s.apply(narrowed);
        } catch (e) {
          // Incompatible shapes (the predicate doesn't apply to this value):
          // fall back to the bare narrowed type rather than failing.
          if (!(e instanceof UnificationError)) throw e;
        }
      }
    }
    // Generalize the narrowed type so its fresh existential fields/element
    // vars (e.g. the `a`/`...r` in a narrowed `{ length :: a, ...r }`, or the
    // element var of a saturated `Array a`) stay polymorphic: each use in the
    // true branch instantiates a fresh copy, so unifying one occurrence (e.g.
    // `return foldable.length`) does not pin the binding's field type.
    consEnv = consEnv.extend(predicate.varName, generalize(env, narrowed));
    if (predicate.unionRemainder) {
      altEnv = altEnv.extend(predicate.varName, mono(predicate.unionRemainder));
    }
    return { consEnv, altEnv };
  }

  // 3. Logical OR: if (isPerson(x) || isString(x)) → narrows to (Person | String)
  if (test.type === 'LogicalExpression' && test.operator === '||') {
    const predicates = collectOrPredicates(subst, test, env);
    if (predicates.length >= 2) {
      // Group by variable name
      const byVar = new Map<string, Type[]>();
      for (const p of predicates) {
        const existing = byVar.get(p.varName) ?? [];
        existing.push(p.narrowedType);
        byVar.set(p.varName, existing);
      }
      for (const [varName, types] of byVar) {
        if (types.length >= 2) {
          consEnv = consEnv.extend(varName, mono(tUnion(types)));
        } else {
          consEnv = consEnv.extend(varName, mono(types[0]));
        }
      }
      return { consEnv, altEnv };
    }
  }

  // 3a. Compound tests.  `A || B` is false only when both are false, so the
  //     else-branch — and the code after a guard `if (A || B) return;` —
  //     gets both alternates (`if (names.length < 2 || link == null) return;`
  //     leaves `link` non-null).  `A && B` is true only when both are true,
  //     so the then-branch gets both consequents.  The other branch stays
  //     un-narrowed: either side may have decided it.
  if (test.type === 'LogicalExpression' && (test.operator === '||' || test.operator === '&&')) {
    const left = computeNarrowedEnvs(subst, test.left, env, annotationMap);
    if (test.operator === '||') {
      const right = computeNarrowedEnvs(subst, test.right, left.altEnv, annotationMap);
      return { consEnv, altEnv: right.altEnv };
    }
    const right = computeNarrowedEnvs(subst, test.right, left.consEnv, annotationMap);
    return { consEnv: right.consEnv, altEnv };
  }

  // 3a'. `m.has (k)` (possibly negated): the branch where it holds may read
  //      `m.get (k)` without the `| Undefined` of a miss.
  {
    let target: AstNode = test;
    let positive = true;
    while (target.type === 'UnaryExpression' && (target as unknown as estree.UnaryExpression).operator === '!') {
      positive = !positive;
      target = (target as unknown as estree.UnaryExpression).argument as AstNode;
    }
    const has = methodCallOf(target, 'has');
    const marker = has ? presentKeyMarker(has.map, has.key) : null;
    if (marker) {
      if (positive) consEnv = consEnv.extend(marker, mono(tBool));
      else altEnv = altEnv.extend(marker, mono(tBool));
      return { consEnv, altEnv };
    }
  }

  // 3b. Builtin `Array.isArray (x)` — the same narrowing as a
  //     `::narrow Array` predicate: a union keeps its Array members (the
  //     else-branch the rest), and an abstract `f a` reads as `[a]` in the
  //     true branch (with `f ≡ Array` there, see `localKindEqsForGuard`).
  if (test.type === 'CallExpression'
      && test.callee?.type === 'MemberExpression' && !test.callee.computed
      && test.callee.object?.type === 'Identifier' && test.callee.object.name === 'Array'
      && test.callee.property?.type === 'Identifier' && test.callee.property.name === 'isArray'
      && test.arguments?.length === 1 && test.arguments[0].type === 'Identifier') {
    const varName = test.arguments[0].name as string;
    const scheme = env.lookup(varName);
    if (scheme) {
      const t: Type = subst.apply(scheme.type);
      const isArr = (m: Type): boolean => m.tag === 'TCon' && m.name === T_ARRAY;
      const kvApp = t.tag === 'TCon' && t.args.length === 1 && !!parseKvName(t.name);
      if (!kvApp && isUnion(t)) {
        const yes = filterUnion(t, isArr);
        const no = filterUnion(t, m => !isArr(m));
        if (!structuralEquals(yes, t)) consEnv = consEnv.extend(varName, mono(yes));
        if (!structuralEquals(no, t)) altEnv = altEnv.extend(varName, mono(no));
        return { consEnv, altEnv };
      }
      if (kvApp) {
        consEnv = consEnv.extend(varName, mono(tCon(T_ARRAY, (t as Type & { tag: 'TCon' }).args)));
        return { consEnv, altEnv };
      }
    }
  }

  // 4. ::narrow on member expression: if (f.isLeft) where isLeft has ::narrow Left
  //    Also handles method calls: if (f.isLeft()) where isLeft has ::narrow Left
  const narrowMemberResult = extractNarrowMemberExpression(test, env, subst, annotationMap, consEnv, altEnv);
  if (narrowMemberResult) return narrowMemberResult;

  // 5. Truthiness: if (x) or if (obj.prop) / if (obj["prop"]) where the
  //    referenced binding (or field) has Null/Undefined in a union.
  //    Also handle negated forms: if (!x), if (!obj.prop) — swap branches.
  {
    let target: AstNode = test;
    let isPositive = true;
    while (target.type === 'UnaryExpression' && target.operator === '!') {
      isPositive = !isPositive;
      target = target.argument;
    }

    const applyToConsequent = (varName: string, narrowedScheme: Type): void => {
      if (isPositive) consEnv = consEnv.extend(varName, mono(narrowedScheme));
      else altEnv = altEnv.extend(varName, mono(narrowedScheme));
    };

    if (target.type === 'Identifier') {
      const varScheme = env.lookup(target.name as string);
      if (varScheme) {
        const resolvedType = subst.apply(varScheme.type);
        const narrowed = removeNullUndefined(resolvedType);
        if (!structuralEquals(narrowed, resolvedType)) {
          applyToConsequent(target.name as string, narrowed);
        }
      }
    } else if (target.type === 'MemberExpression'
               && target.object.type === 'Identifier') {
      // Extract the property name for both non-computed (`obj.prop`) and
      // computed-with-string-literal (`obj["prop"]`) forms.  Other
      // shapes (computed variable key, deep paths, optional chaining)
      // are intentionally not handled here.
      let propName: string | null = null;
      if (!target.computed && target.property.type === 'Identifier') {
        propName = target.property.name as string;
      } else if (target.computed && target.property.type === 'Literal'
                 && typeof (target.property as estree.Literal).value === 'string') {
        propName = (target.property as estree.Literal).value as string;
      }
      if (propName) {
        const objName = (target.object as estree.Identifier).name as string;
        const objScheme = env.lookup(objName);
        if (objScheme) {
          const resolvedObj = subst.apply(objScheme.type);
          const expandedObj = resolvedObj.tag === 'TRecord' ? resolvedObj : resolvedObj;
          if (expandedObj.tag === 'TRecord'
              && Object.prototype.hasOwnProperty.call(expandedObj.fields, propName)) {
            const fieldType = expandedObj.fields[propName];
            const narrowedField = removeNullUndefined(subst.apply(fieldType));
            if (!structuralEquals(narrowedField, subst.apply(fieldType))) {
              const narrowedRecord: Type = {
                ...expandedObj,
                fields: { ...expandedObj.fields, [propName]: narrowedField },
              };
              applyToConsequent(objName, narrowedRecord);
            }
          }
        }
      }
    }
  }

  return { consEnv, altEnv };
}

// ---------------------------------------------------------------------------
// Literal guard / conditional return
// ---------------------------------------------------------------------------

/**
 * Extract literal equality or truthiness guard info from a function body.
 * Detects patterns like:
 *   if (param === literal) { return T; } ... return T2;
 *   if (param) { return T; } ... return T2;
 * where the if-statement is a guard clause (no alternate, consequent always returns).
 *
 * Returns { paramIndex, matchReturnTypeStr, literalValue?, isTruthiness? } if found.
 *
 * @param subst - Current substitution for resolving types
 * @param body - The function body AST node
 * @param paramNames - Parameter names in order
 * @param collectAllReturnTypes - Callback to collect return types from a block
 */
export function extractLiteralGuardReturnInfo(
  subst: Substitution,
  body: AstNode,
  paramNames: string[],
  collectAllReturnTypes: (node: AstNode) => Type[],
): { paramIndex: number; matchReturnTypeStr: string; literalValue?: string | number | boolean | bigint | RegExp | null; isTruthiness?: boolean } | null {
  if (body.type !== 'BlockStatement') return null;

  for (const stmt of (body.body ?? [])) {
    if (stmt.type !== 'IfStatement') continue;
    if (stmt.alternate) continue;
    if (!blockAlwaysReturns(stmt.consequent)) continue;

    const test = stmt.test;
    let paramName: string | null = null;
    let literalValue: string | number | boolean | bigint | RegExp | null | undefined = undefined;
    let isTruthiness = false;

    if (test.type === 'BinaryExpression' && (test.operator === '===' || test.operator === '==')) {
      // Pattern: param === literal  or  literal === param
      if (test.left.type === 'Identifier' && test.right.type === 'Literal') {
        paramName = test.left.name as string;
        literalValue = test.right.value;
      } else if (test.right.type === 'Identifier' && test.left.type === 'Literal') {
        paramName = test.right.name as string;
        literalValue = test.left.value;
      }
    } else if (test.type === 'Identifier') {
      // Pattern: if (param) — truthiness guard
      paramName = test.name as string;
      isTruthiness = true;
    }

    if (paramName === null) continue;
    if (!isTruthiness && (literalValue === undefined || literalValue === null)) continue;

    const paramIndex = paramNames.indexOf(paramName);
    if (paramIndex < 0) continue;

    // Collect return types from the guard's consequent
    const returnTypes = collectAllReturnTypes(stmt.consequent);
    if (returnTypes.length === 0) continue;

    // Resolve and serialize the matching return type
    const matchReturnType = subst.apply(returnTypes[0]);
    const matchReturnTypeStr = typeToString(matchReturnType);

    if (isTruthiness) {
      return { paramIndex, matchReturnTypeStr, isTruthiness: true };
    }
    return { paramIndex, matchReturnTypeStr, literalValue };
  }

  return null;
}

/**
 * Apply conditional return narrowing at a call site.
 * If the callee has a `conditionalReturn` on its scheme, and the argument
 * at the matching position satisfies the guard, narrow the return type
 * union to keep only the matching branch type.
 */
export function applyConditionalReturnNarrowing(
  subst: Substitution,
  node: estree.CallExpression,
  env: TypeEnv,
  result: Type,
): Type {
  if (node.callee?.type !== 'Identifier') return result;

  const calleeScheme = env.lookup(node.callee.name as string);
  if (!calleeScheme?.conditionalReturn) return result;

  const cr = calleeScheme.conditionalReturn;
  const { paramIndex, matchReturnTypeStr } = cr;

  // Check if the argument at paramIndex matches the guard
  if (paramIndex >= node.arguments.length) return result;
  const arg = node.arguments[paramIndex];

  // Determine if the argument is a known literal (so we can narrow)
  const isArgLiteral = arg.type === 'Literal' ||
    (arg.type === 'Identifier' && (arg.name === 'true' || arg.name === 'false' ||
     arg.name === 'undefined' || arg.name === 'NaN'));

  if (!isArgLiteral) return result;

  let guardSatisfied: boolean;

  if (cr.isTruthiness) {
    // Truthiness guard: satisfied if the arg is a truthy literal
    guardSatisfied = isLiteralTruthy(arg);
  } else {
    // Equality guard: satisfied if the arg literal matches the stored value
    let argLiteralValue: string | number | boolean | bigint | RegExp | null | undefined = undefined;
    if (arg.type === 'Literal') {
      argLiteralValue = arg.value;
    } else if (arg.type === 'Identifier') {
      if (arg.name === 'true') argLiteralValue = true;
    }
    guardSatisfied = argLiteralValue !== undefined && argLiteralValue === cr.literalValue;
  }

  if (guardSatisfied) {
    // Guard matched: keep only the match branch return type
    return narrowDeepUnionResult(subst, result, matchReturnTypeStr, 'keep');
  } else {
    // Guard NOT matched: remove the match branch return type, keep the rest
    return narrowDeepUnionResult(subst, result, matchReturnTypeStr, 'remove');
  }
}

/**
 * Navigate through nested TFun types to find the deepest result type.
 * If it's a union, filter members based on mode:
 *   'keep'   — keep only members matching matchReturnTypeStr
 *   'remove' — remove members matching matchReturnTypeStr
 */
export function narrowDeepUnionResult(subst: Substitution, type: Type, matchReturnTypeStr: string, mode: 'keep' | 'remove'): Type {
  const resolved = subst.apply(type);

  if (resolved.tag === 'TFun') {
    const narrowedResult = narrowDeepUnionResult(subst, resolved.result, matchReturnTypeStr, mode);
    return tFun(resolved.param, narrowedResult);
  }

  if (isUnion(resolved)) {
    const filtered = resolved.args.filter(a => {
      const memberStr = typeToString(subst.apply(a));
      return mode === 'keep'
        ? memberStr === matchReturnTypeStr
        : memberStr !== matchReturnTypeStr;
    });
    if (filtered.length > 0 && filtered.length < resolved.args.length) {
      return filtered.length === 1 ? filtered[0] : tUnion(filtered);
    }
  }

  return resolved;
}

// ---------------------------------------------------------------------------
// Pure AST utility helpers
// ---------------------------------------------------------------------------

/**
 * Detect whether a block body contains `this.x = ...` assignment
 * expressions, which is the hallmark of a constructor function.
 * Uses an ancestor walk so `this` belonging to NESTED functions (which have
 * their own `this`) does not count — only assignments whose nearest
 * enclosing function boundary is outside `block` (or an arrow, which
 * inherits `this`) are the block's own.
 */
/**
 * `function Name (…) { if (!(this instanceof Name)) return new Name (…); … }`
 * — a constructor that guards itself, so calling it WITHOUT `new` is safe
 * (it re-invokes itself with `new`).  Such a function must not be flagged by
 * the "must be called with 'new'" check.
 */
export function hasSelfNewGuard(block: AstNode, name: string): boolean {
  const first = (((block as { body?: unknown }).body ?? []) as AstNode[])[0];
  if (!first || first.type !== 'IfStatement') return false;
  const test = first.test as AstNode;
  if (test.type !== 'UnaryExpression' || test.operator !== '!') return false;
  const inner = test.argument as AstNode;
  if (inner.type !== 'BinaryExpression' || inner.operator !== 'instanceof') return false;
  if (inner.left?.type !== 'ThisExpression') return false;
  if (inner.right?.type !== 'Identifier' || inner.right.name !== name) return false;
  let ret = first.consequent as AstNode;
  const retBody = (ret as { body?: unknown }).body as AstNode[] | undefined;
  if (ret.type === 'BlockStatement' && retBody?.length === 1) ret = retBody[0];
  return ret.type === 'ReturnStatement'
    && ret.argument?.type === 'NewExpression'
    && ret.argument.callee?.type === 'Identifier'
    && ret.argument.callee.name === name;
}

export function blockHasThisAssignment(block: AstNode): boolean {
  let found = false;
  walk.ancestor(block, {
    AssignmentExpression(node: any, _state: unknown, ancestors: readonly AstNode[]) {
      if (node.left?.type === 'MemberExpression'
          && node.left.object?.type === 'ThisExpression'
          // Private-field assignments (`this.#x = ...`) are characteristic of
          // class methods mutating internal state — not constructor-style
          // public field initialisation — so they should not flip the function
          // into "implicitly returns this" mode.
          && node.left.property?.type !== 'PrivateIdentifier') {
        // Walk ancestors from the assignment inward-out: if a nested
        // function/class boundary (which rebinds `this`) sits between the
        // block and the assignment, the `this` is not ours.
        let rebound = false;
        for (const anc of ancestors) {
          if (anc === block) { rebound = false; continue; }
          const t = (anc as { type?: string }).type;
          if (t === 'FunctionDeclaration' || t === 'FunctionExpression' || t === 'ClassDeclaration' || t === 'ClassExpression') {
            rebound = true;
          }
        }
        if (!rebound) found = true;
      }
    },
  });
  return found;
}

/** Check if a node is a `require('specifier')` call. */
export function isRequireCall(node: AstNode | null | undefined): boolean {
  return (
    node?.type === 'CallExpression' &&
    node.callee?.type === 'Identifier' &&
    node.callee.name === 'require' &&
    node.arguments?.length === 1 &&
    node.arguments[0]?.type === 'Literal' &&
    typeof node.arguments[0].value === 'string'
  );
}

/** Resolve a require() call via an import resolver. */
export function resolveRequire(
  importResolver: ((specifier: string) => Map<string, import('../hm/types').Scheme> | { kind: 'untyped' } | null) | null,
  node: estree.CallExpression,
): Map<string, import('../hm/types').Scheme> | { kind: 'untyped' } | null {
  if (!importResolver) return null;
  const specifier = (node.arguments[0] as estree.Literal).value as string;
  return importResolver(specifier);
}

// ---------------------------------------------------------------------------
// Sumtype variant property narrowing
// ---------------------------------------------------------------------------

/**
 * Narrow a union property type within a sumtype variant class.
 *
 * When inside a variant (e.g. Right) and the property type is a union
 * whose members correspond to the sumtype's type parameters (e.g. (e | a)
 * for Either e a), narrow to only the parameters carried by this variant.
 *
 * Example: sumtype Either e a = Left e | Right a
 *   Either#$value :: Either e a ~> (e | a)
 *   In Right context: narrows (e | a) → a
 *   In Left context: narrows (e | a) → e
 */
export function narrowSumtypePropertyUnion(
  methodType: Type,
  resolved: Type,
  methodArgs: Type[],
  env: TypeEnv,
  envKey: string = '__sumtypeVariant',
): Type {
  const variantScheme = env.lookup(envKey);
  if (!variantScheme) return methodType;

  const variantType = instantiate(variantScheme);

  // Collect variant names — either a single TCon or a union of TCon markers
  const variantNames: string[] = [];
  if (variantType.tag === 'TCon') {
    if (variantType.name === T_UNION) {
      for (const member of variantType.args) {
        if (member.tag === 'TCon') variantNames.push(member.name);
      }
    } else {
      variantNames.push(variantType.name);
    }
  }
  if (variantNames.length === 0) return methodType;

  const parentName = getParentTypeName(variantNames[0]);
  if (!parentName || resolved.tag !== 'TCon' || resolved.name !== parentName) return methodType;

  const dt = getDataType(parentName);
  if (!dt) return methodType;

  // Get the indices of type params carried by ANY of the variant(s)
  const carriedIndices = new Set<number>();
  for (const vName of variantNames) {
    const variant = dt.variantMap.get(vName);
    if (!variant || variant.fields.length === 0) return methodType;
    for (const field of variant.fields) {
      const idx = dt.decl.typeVars.indexOf(field);
      if (idx >= 0) carriedIndices.add(idx);
    }
  }

  // If variant carries all params, no narrowing needed
  if (carriedIndices.size === dt.decl.typeVars.length) return methodType;

  // The union must have the same number of members as the receiver's type args
  const unionMembers = (methodType as import('../hm/types').TCon).args;
  if (unionMembers.length !== methodArgs.length) return methodType;

  // Match each union member to a type arg by identity
  const narrowed: Type[] = [];
  const used = new Set<number>();
  for (const member of unionMembers) {
    let matchIndex = -1;
    for (let j = 0; j < methodArgs.length; j++) {
      if (used.has(j)) continue;
      if (member.tag === 'TVar' && methodArgs[j].tag === 'TVar' && (member as TVar).id === (methodArgs[j] as TVar).id) {
        matchIndex = j;
        break;
      }
      if (structuralEquals(member, methodArgs[j])) {
        matchIndex = j;
        break;
      }
    }
    if (matchIndex >= 0) used.add(matchIndex);

    if (matchIndex >= 0 && carriedIndices.has(matchIndex)) {
      narrowed.push(member);
    } else if (matchIndex < 0) {
      // Union member doesn't match any type arg — keep it (can't narrow)
      narrowed.push(member);
    }
    // If matchIndex >= 0 but NOT in carriedIndices, filter it out
  }

  if (narrowed.length === 0) return methodType;
  if (narrowed.length === 1) return narrowed[0];
  return tUnion(narrowed);
}
