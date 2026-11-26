// ============================================================================
// Inference — Algorithm W for JavaScript AST nodes
//
// Plain language: this is the conductor of the whole analysis.  The
// `InferenceEngine` class owns all shared state for one file's analysis —
// the environment (names → types), the substitution (placeholder answers),
// the diagnostics list and the annotation maps — and drives the passes:
//   1. setup    — read all comments/annotations/directives (setupPass.ts)
//   2. walk     — visit every statement and expression, inferring types
//                 (statements.ts, expressions.ts, calls.ts, …)
//   3. finish   — validate parked constraints, check annotation promises,
//                 and pack up the result (constraints.ts, results.ts)
// The heavy logic lives in the sibling modules, which receive the engine as
// their first argument; this file wires them together.
//
// "Algorithm W" is the name of the classic Hindley–Milner inference recipe
// this engine follows.
// ============================================================================

import type * as estree from '../estree';
import { parseStrict, parseLoose, describeParseError } from '../parsing';
import {
  Type,
  Scheme,
  tVar,
  tCon,
  tVoid,
  tRow,
  TypeVarAllocator,
  setActiveAllocator,
  collectVarNames,
  AstNode,
  RepEntry,
  SKOLEM_PREFIX,
} from '../hm/types';
import { Substitution } from '../hm/substitution';
import { TypeEnv, defaultEnv, skolemSubstForScheme, collectRowVarIds, collectLabelVarIds } from '../hm/env';
import { TypeAnnotation } from '../commentParser';
import { clearGlobalRegistries } from '../registries/session';
import { scrubSkolems, eachType } from '../hm/typeUtils';
import {
  expandAliases,
  processConstraintDirectives,
  processGlobalDirectives,
  checkAnnotationRigid,
} from './annotations';
import { InferenceDiagnostic, ImportResolver, TypeDirectiveResolver, ImportTypeAliasResolver, InferenceResult, UNTYPED_MODULE, UntypedModule, DiagnosticSink, TypeResolutionContext, NodeTypeRecorder, UnifierContext } from './types';
import { freshVars, computeRestType, findConstructor, exportsToRecord } from './helpers';
import * as stmtFns from './statements';
import * as constraintFns from './constraints';
import * as resultFns from './results';
import { setModuleReps } from './moduleReps';
import * as setupFns from './setupPass';
import * as unifyDiag from './unifyDiag';
import { withAliasExpander } from '../hm/unify';
import * as exprFns from './expressions';
import * as exprMemberFns from './expr-member';
import * as callFns from './calls';
import * as modFns from './modules';

export type { InferenceDiagnostic, ImportResolver, TypeDirectiveResolver, ImportTypeAliasResolver, InferenceResult, UntypedModule };
export { UNTYPED_MODULE };
export { markOpenWorldExports, isOpenWorldExports } from './types';
export { freshVars, computeRestType, findConstructor, exportsToRecord };

// defaultEnv lives in env.ts — re-exported here for backward compatibility
export { defaultEnv };

// -----------------------------------------------------------------------
// Import deduplication — offset-preserving preprocessing
// -----------------------------------------------------------------------

/** Blank duplicate import lines with spaces so the parser doesn't throw
 *  "Identifier 'X' has already been declared" while keeping all offsets stable. */
function deduplicateImports(source: string): string {
  const seen = new Set<string>();
  const re = /^(import\s+(?:(\w+)|(?:\{([^}]+)\})|(?:\*\s+as\s+(\w+)))\s+from\s+['"][^'"]+['"];?\s*)$/gm;
  return source.replace(re, (match, _full, def, named, ns) => {
    const names: string[] = [];
    if (def) names.push(def);
    if (ns) names.push(ns);
    if (named) {
      for (const part of (named as string).split(',')) {
        const t = part.trim();
        const as = t.match(/\w+\s+as\s+(\w+)/);
        names.push(as ? as[1] : t);
      }
    }
    if (names.some(n => seen.has(n))) return match.replace(/[^\n]/g, ' ');
    names.forEach(n => seen.add(n));
    return match;
  });
}

// -----------------------------------------------------------------------
// Helpers
// -----------------------------------------------------------------------

/**
 * Collect `[start, end]` source ranges of every top-level binding in the
 * program — `VariableDeclarator` (incl. inside exports), `FunctionDeclaration`,
 * and `ClassDeclaration`.  Each entry is tagged with whether the binding
 * name matches an entry in the supplied annotation map so the diagnostics
 * service can distinguish "annotated body" vs "any body" suppression.
 *
 * Nested members (class methods, inner functions, deeply-nested
 * declarators) are intentionally NOT enumerated — they are already covered
 * by their enclosing top-level binding's extent.
 */
function collectTopLevelBindingExtents(
  ast: estree.Program,
  annotations: Map<string, TypeAnnotation>,
): Array<{ start: number; end: number; annotated: boolean }> {
  const out: Array<{ start: number; end: number; annotated: boolean }> = [];

  const hasAnyAnnotation = (name: string): boolean => {
    if (annotations.has(name)) return true;
    // Method/sumtype style: `Foo#bar`, `Foo.bar`, `Foo$prototype$bar`.
    for (const key of annotations.keys()) {
      if (key.startsWith(name + '#') || key.startsWith(name + '.') || key.startsWith(name + '$prototype$')) {
        return true;
      }
    }
    return false;
  };

  for (const rawStmt of ast.body) {
    const stmt = (rawStmt.type === 'ExportNamedDeclaration' || rawStmt.type === 'ExportDefaultDeclaration')
      && rawStmt.declaration ? rawStmt.declaration : rawStmt;

    if (stmt.type === 'VariableDeclaration') {
      for (const declarator of stmt.declarations) {
        if (!declarator.init) continue;
        const id = declarator.id as estree.Identifier;
        const name = id?.name;
        if (!name) continue;
        out.push({ start: declarator.start, end: declarator.end, annotated: hasAnyAnnotation(name) });
      }
      continue;
    }
    if (stmt.type === 'FunctionDeclaration' && stmt.id?.name) {
      out.push({ start: stmt.start, end: stmt.end, annotated: hasAnyAnnotation(stmt.id.name) });
      continue;
    }
    if (stmt.type === 'ClassDeclaration' && stmt.id?.name) {
      out.push({ start: stmt.start, end: stmt.end, annotated: hasAnyAnnotation(stmt.id.name) });
      continue;
    }
  }

  return out;
}

// -----------------------------------------------------------------------
// The inference engine
// -----------------------------------------------------------------------

export class InferenceEngine implements DiagnosticSink, TypeResolutionContext, NodeTypeRecorder, UnifierContext {
  /** @internal */ subst = new Substitution();
  /** @internal */ diagnostics: InferenceDiagnostic[] = [];
  /** @internal */ nodeTypes = new Map<number, { type: Type, end: number }>();
  /** @internal Map from a top-level binding declaration's start offset to its
   *  generalized scheme. Hover uses this to display the generic type of a
   *  polymorphic binding at its declaration site, instead of the live
   *  substitution-applied node type which downstream call sites may have
   *  specialized (e.g. a generic `getPath` shown with a concrete record). */
  declaredSchemes = new Map<number, Scheme>();
  /** @internal */ annotationMap = new Map<string, TypeAnnotation>();
  /** @internal */ annotationByOffset = new Map<number, TypeAnnotation>();
  /** @internal */ methodSignatures = new Map<number, string>();
  /** @internal Maps every rigid skolem name (`§N`) minted while checking an
   *  annotated function body back to the annotation's display letter, so
   *  skolems can be scrubbed out of hover types and diagnostic messages. */
  skolemDisplayNames = new Map<string, string>();
  /** @internal Origin (annotation name + comment range) of each rigid skolem.
   *  Used to attach related-information to a diagnostic when two DISTINCT
   *  skolems carrying the SAME display letter (e.g. the `a` of a method
   *  annotation vs the `a` of the enclosing factory's signature) collide in
   *  one message. */
  skolemOrigins = new Map<string, { name?: string; start: number; end: number }>();
  /** @internal Stack of the annotated RETURN types of the function(s) whose
   *  bodies are currently being inferred.  Lets a nested method annotation
   *  (`Type#m :: Type e a ~> …` above a const inside a factory returning
   *  `Type e a`) link its receiver variables to the factory's own signature
   *  variables — the record under construction IS the receiver. */
  enclosingAnnotatedReturns: Type[] = [];
  /** @internal */ importResolver: ImportResolver | null = null;
  /** @internal */ typeDirectiveResolver: TypeDirectiveResolver | null = null;
  /** @internal */ importTypeAliasResolver: ImportTypeAliasResolver | null = null;
  /** @internal Names explicitly exported via `export`, `module.exports`, or `exports.X`. */
  exportedNames = new Set<string>();
  /** @internal Inferred RHS type for `exports.X = expr` assignments — used when X is not bound in env. */
  cjsExportTypes = new Map<string, Type>();
  /**
   * @internal Names exported through `module.exports = { key: <expr> }` whose
   * value is NOT the same-named identifier: the export's type is the
   * property VALUE's type (from {@link cjsExportTypes}), never an unrelated
   * env binding that happens to share the key's name.
   */
  cjsValueExports = new Set<string>();
  /** @internal Type of `module.exports = { … }` — the CommonJS module value, exported as `default` for ESM interop. */
  cjsObjectExportType: Type | null = null;
  /** @internal The module uses CommonJS exports (`module.exports…` / `exports.X`). */
  usesCjsExports = false;
  /**
   * @internal Unannotated static-member assignments `Obj.prop = <fn>` keyed by
   * object identifier name -> (property name -> resolved function type).  Used
   * by `buildExportMap` so a default export's static factories (e.g.
   * `Response.Redirect = _Redirect;`) are exported cross-file even without an
   * explicit `// Response.Redirect :: ...` annotation.
   */
  staticMemberTypes = new Map<string, Map<string, Type>>();
  /** @internal Pending constraint checks: maps fresh type var id -> { constraintName, node } */
  pendingConstraints: { varId: number; constraintName: string; node: AstNode; reps?: RepEntry[]; given?: boolean; typeVarName?: string; appliedArgNames?: string[]; annStart?: number; annEnd?: number }[] = [];
  /** @internal `::rep` directives parsed from the current file (constraint representations). */
  fileReps: RepEntry[] = [];
  /** @internal `::rep` representatives collected from imported schemes.  These
   *  let an imported constrained function's reps satisfy constraint checks in
   *  the importing file (and propagate further on re-export). */
  importedReps: RepEntry[] = [];
  /** @internal Pending structural-union constraint checks. The constrained
   *  type variable must unify with one of the listed alternatives. */
  pendingUnionConstraints: { varId: number; alternatives: Type[]; displayName: string; node: AstNode }[] = [];
  /** @internal Map from kind-variable id to constraint names (for hover/completion). */
  kvConstraints = new Map<number, string[]>();
  /** @internal Rank-N: skolem name → constraint classes promised by the
   *  `forall` that minted it (incl. superclass closure).  A pending
   *  constraint that resolves to such a skolem and is promised is satisfied. */
  rankNSkolemPromises = new Map<string, Set<string>>();
  /** @internal Map from kind-variable id to applied constraint names (constraints on the constructor, e.g. Monoid (f a)). */
  kvConstructorConstraints = new Map<number, string[]>();
  /** @internal Constraint constructor rewrites: function types to replace with constructors in post-processing. */
  constraintConstructorRewrites: { from: Type; to: Type }[] = [];
  /** @internal When true, auto-union is suppressed (inside annotated declarations). */
  suppressAutoUnion = false;
  /** @internal Var ids that must survive per-element freshening of expanded
   *  union element types in array literals.  Set by call inference to the
   *  free vars of the callee's result type: a var occurring both in the
   *  element union and the result (e.g. the params var `p` in
   *  `[Selector p] -> Tag p o`) threads element contributions into the
   *  result, so freshening it per element would sever the link. */
  pinnedElementVarIds: Set<number> | null = null;
  /** @internal Stack of yielded-type collectors, one frame per generator
   *  function currently being inferred.  The `YieldExpression` inference case
   *  pushes each yielded value type onto the top frame so the function's
   *  caller-visible return type can be modelled as `Generator <yield>`. */
  generatorYieldStack: Type[][] = [];
  /** @internal Names of bindings that are generator functions (`function* f`,
   *  `const f = function* () {}`).  A call to one of these names yields a
   *  `Generator <element>` value rather than the function's element type. */
  generatorFunctionNames = new Set<string>();
  /** @internal When true, suppress "Infinite type" diagnostics (annotated constrained self-recursion). */
  suppressInfiniteType = false;
  /** @internal When >0, `poisonFreeVars` is a no-op.  Set during speculative
   *  overload-branch trials so a nested unification failure does not bake the
   *  `$error` sentinel into a captured branch remainder (the substitution is
   *  rolled back anyway; any genuine failure re-surfaces when a branch is
   *  actually committed). */
  suppressPoisonDepth = 0;
  /** @internal Name of the top-level binding whose initializer is currently being inferred.
   *  Used to attribute an infinite-type (occurs-check) diagnostic to the binding
   *  (e.g. "applyArgs has an infinite type ..."). */
  currentBindingName: string | undefined = undefined;
  /** @internal Set when an infinite type error was suppressed during constrained annotation body inference. */
  infiniteTypeSuppressedDuringAnnotation = false;
  /** @internal Monotonic counter bumped each time the occurs check (infinite type)
   *  fires in `unifyWithDiagnostic`.  Used to detect whether a binding's body
   *  inference produced an infinite type so the signature can overrule the
   *  downstream annotation-vs-body mismatch. */
  occursCheckCount = 0;
  /** @internal applyArgs-style peeling side-table.  When a concrete curried
   *  function is applied to a combinator whose parameter is a spread arrow
   *  chain `(a -> b -> ... -> z)` and whose result is a spread-array applier
   *  `[a, b, ...] -> z`, we record the function's flattened parameter list and
   *  terminal result keyed by the (inner) call node.  The subsequent array
   *  application looks this up via `node.callee` to derive the peeled result
   *  type (partial application) and flag over-application. */
  spreadChainPeel = new Map<unknown, { params: Type[]; result: Type }>();
  /** @internal Type aliases: uppercase names mapped to their aliased type (e.g. Person -> { name: String, age: Number }). */
  typeAliases = new Map<string, Type>();
  /** @internal Type alias var names for polymorphic expansion (e.g. TypedArray -> ['a', 'b']). */
  typeAliasVars = new Map<string, string[]>();
  /** @internal Constructor / callable-value annotations imported from
   *  sidecars or project overrides.  Consulted by `tryConstructorCallable`
   *  when a value of an uppercase TCon is invoked but the local
   *  `annotationMap` has no entry for that name (typical for values
   *  returned from a third-party package and called locally). */
  importedConstructors = new Map<string, Scheme>();
  /** @internal Instance-callable schemes, declared via `Name() :: T`.
   *  An entry's array contains every overload declared for that name in
   *  declaration order, merged from the local source and any imported
   *  sidecars (local entries take precedence on name collision).
   *  Consulted by `tryConstructorCallable` and by hover / signature help
   *  when a value of an uppercase TCon (e.g. `QueryTag {row}`) is invoked
   *  or its overloads are surfaced. */
  instanceCallables = new Map<string, Scheme[]>();
  /** @internal `[start, end]` source ranges of every top-level binding the
   *  engine recognizes (`VariableDeclarator`, `FunctionDeclaration`,
   *  `ClassDeclaration`).  Populated from the AST after a successful parse
   *  and surfaced on the result for `trustAnnotations: 'all-bodies'`. */
  bindingExtents: Array<{ start: number; end: number; annotated: boolean }> = [];
  /** @internal Map from AST node end offset to its inferred type. Used for completion after call expressions. */
  nodeTypesByEnd = new Map<number, { type: Type, start: number }>();
  /** @internal Map from an arrow/function-expression node's start offset to its
   *  inferred FUNCTION type.  Recorded separately from {@link nodeTypes}
   *  because a function's start offset collides with its first parameter
   *  identifier (which wins in `nodeTypes` for hover).  Hover uses this map to
   *  pick the tightest enclosing function scope when seeding display-letter
   *  assignment, so sibling body-local bindings get distinct, source-ordered
   *  letters (`n :: b`, `xs :: c`) instead of each independently grabbing the
   *  next free letter. */
  functionNodeTypes = new Map<number, { type: Type, end: number }>();
  /** @internal Identifier name from `module.exports = X` or `export default X` for default export resolution. */
  defaultExportName: string | null = null;
  /** @internal Maps local binding name to the import specifier it came from (for default imports). */
  defaultImportSources = new Map<string, string>();
  /** @internal Names of auto-detected curry wrapper functions (from spread-tuple type signatures). */
  curryFunctionNames = new Set<string>();
  /** curryN-style wrappers: name → number of leading arguments. */
  curryNFunctionNames = new Map<string, number>();
  /** @internal Maps a dotted member-assignment name (`Param.Path`) to the
   *  0-based indices of trailing function parameters with JS body defaults.
   *  Consulted by call-site arity checks for `obj.prop(...)` so that
   *  trailing missing args are accepted when the implementation marks
   *  them optional via `(x = …)`. */
  optionalParamSlotsByDottedName = new Map<string, number[]>();
  /** @internal After a curry wrapper call, this holds true to mark the next variable binding as curried. */
  pendingIsCurriedResult = false;
  /** @internal Pending conditional return info detected during function body inference. */
  pendingConditionalReturn: { paramIndex: number; matchReturnTypeStr: string; literalValue?: string | number | boolean | bigint | RegExp | null; isTruthiness?: boolean } | null = null;
  /** @internal Set of node start offsets whose bindings are curried. */
  curriedNodes = new Set<number>();
  /** @internal Maps a call's callee start offset to the index of the
   *  overload branch that matched the actual arguments (for hover /
   *  signature help to surface only the selected overload). */
  callSiteOverloadIndex = new Map<number, number>();
  /** @internal Set of offsets where an unbound-variable diagnostic was raised. */
  unboundIdentifiers = new Set<number>();
  /** @internal Set of offsets where property access occurred on an unconstrained type variable. */
  unconstrainedPropAccesses = new Set<number>();
  /** @internal Property accesses on a still-unresolved TVar receiver, parked
   *  for late re-resolution.  When later unification pins the receiver to a
   *  concrete type (e.g. the data argument of a curried annotated `map`
   *  arriving AFTER the callback), the member is looked up again and its
   *  type is unified with the placeholder result var — so `s => s.length`
   *  resolves to `String -> Number` instead of staying `s -> b`. */
  deferredMemberAccesses: Array<{ objType: Type; propName: string; resultType: Type; propStart: number; node: AstNode }> = [];
  /** @internal Set of `TypeName#propName` for properties assigned via `this.prop = ...` in constructors. */
  constructorProperties = new Set<string>();
  /** @internal Map of `TypeName##privateName` -> Type for private class fields and methods. */
  privateClassMembers = new Map<string, Type>();
  /**
   * @internal Provenance of top-level constructor-like bindings, used to
   * decide how `.constructor` should be typed and whether `new` is required.
   * - `'class'`           : `class Foo { ... }`
   * - `'function-this'`   : `function Foo(){ this.x = ... }` style constructor
   * - `'arrow-factory'`   : `const Foo = (...) => ({...})` — runtime returns Object
   * - `'sumtype'`         : registered `@sumtype` root name
   * - `'sumtype-variant'` : variant of an `@sumtype` declaration
   */
  constructorProvenance = new Map<string, 'class' | 'function-this' | 'arrow-factory' | 'sumtype' | 'sumtype-variant'>();
  /**
   * @internal Map from a `.constructor` property-node start offset to the
   * parent sumtype name (e.g. `Maybe`).  Populated by
   * `inferTConConstructorAccess` so hover can surface the parent sumtype
   * declaration alongside the constructor's type.
   */
  constructorParentSumtype = new Map<number, string>();
  /**
   * @internal Map from a `.constructor` property-node start offset to the
   * built-in type name (`'Array'`, `'Function'`, …) when the access was
   * resolved via `builtinConstructorType`.  Used by call-site logic to
   * specialise the return type (e.g. widen `Array(...)` to a union of arg
   * element types) without piping the receiver through unification.
   */
  builtinCtorKind = new Map<number, string>();
  /**
   * @internal Name-keyed propagation of `builtinCtorKind`.  When a
   * declarator's init is a `.constructor` access tagged with a builtin
   * kind, the declared name maps to that kind so subsequent call sites
   * (`const ac = [].constructor; ac(1,2)`) can specialise.  Names are
   * module-scoped (last write wins) — this is best-effort, not lexical.
   */
  builtinCtorByVarName = new Map<string, string>();
  /** @internal See InferenceResult.frozenPropertyTypeStr. */
  frozenPropertyTypeStr = new Map<number, string>();
  /** @internal See InferenceResult.frozenParamType. */
  frozenParamType = new Map<number, Type>();
  /** @internal When set, union-vs-expected diagnostics report on this node (the enclosing annotated method). */
  annotationMethodNode: AstNode | null = null;
  /** Function node whose annotation is checked by its enclosing `const`
   *  binding (body skolemized via annotationByOffset, validated in
   *  stmt-bindings like a `function` declaration) — the inline-annotation
   *  validation in inferFunctionExpression skips it. */
  annotationCheckedByBinding: AstNode | null = null;
  /** Lexically scoped annotation type variables (letter → enclosing body
   *  skolem); see inferFunctionExpression in expr-functions.ts. */
  scopedTypeVars: Map<string, Type> = new Map();
  /** Row variables of the parameters of the functions whose bodies are
   *  being checked against their own annotation.  Reading a field outside
   *  such a row is an error; a row that is not in this set gains the field
   *  (see the open-record case in expr-member.ts). */
  rigidRowIds: Set<number> = new Set();
  /** Local type equalities in force while inferring the true branch of a
   *  `::narrow C` guard on a value of abstract type `f a` (`isArray (xs)`
   *  with `xs :: f a`): `f ≡ C` holds INSIDE the branch only.  A `return`
   *  there of type `C x` is re-expressed as `f x` (see `returnTypeOverrides`)
   *  so the branch never pins `f` for the whole function. */
  localKindEqs: { varId: number; varName: string; con: string; arity: number }[] = [];
  /** The inferred type of each `return` statement inferred through the
   *  statement path (re-expressed under `localKindEqs` where they apply). */
  returnTypeOverrides = new Map<AstNode, Type>();
  /** Each declaration's own annotation (overloads merged), by node start —
   *  see `buildAnnotationsByDeclaration`. */
  annotationsByDeclaration: Map<number, TypeAnnotation> = new Map();
  /** @internal Bound version of addDiag for passing to helpers. */
  readonly boundAddDiag = this.addDiag.bind(this);

  /**
   * Per-engine type-variable allocator.  Installed as the *active* allocator
   * at the start of {@link infer} so that every `tVar()` call during this
   * run uses this engine's counter.
   */
  readonly allocator = new TypeVarAllocator();

  /**
   * Project-level globals source (from `globals.hm` or configured file).
   * Set once by the server; used automatically by every `infer()` call.
   */
  globalsSource: string | null = null;
  /** `::global` members from the globals file (re-registered with aliases
   *  expanded during setup). */
  globalDirectiveMethods: { name: string; ann: import('../commentParser').TypeAnnotation }[] = [];

  /**
   * Infer types for a JavaScript source string.
   * @param source       The JavaScript source code
   * @param env          Optional base type environment
   * @param importResolver  Optional callback to resolve import specifiers to exported types
   * @param typeDirectiveResolver  Optional callback to resolve `// ::types` directives to source code
   * @param importTypeAliasResolver  Optional callback to resolve import specifiers to type aliases
   */
  infer(source: string, env?: TypeEnv, importResolver?: ImportResolver, typeDirectiveResolver?: TypeDirectiveResolver, importTypeAliasResolver?: ImportTypeAliasResolver): InferenceResult {
    // Unify may expand a bare alias name of this file (a recursive alias,
    // a name inside an imported type) when it would otherwise fail.
    return withAliasExpander(
      t => this.maybeExpandAlias(t),
      () => this.inferInScope(source, env, importResolver, typeDirectiveResolver, importTypeAliasResolver),
    );
  }

  private inferInScope(source: string, env?: TypeEnv, importResolver?: ImportResolver, typeDirectiveResolver?: TypeDirectiveResolver, importTypeAliasResolver?: ImportTypeAliasResolver): InferenceResult {
    // Pre-process: remove duplicate import declarations so the parser doesn't
    // throw "Identifier 'X' has already been declared".  Offsets stay stable.
    source = deduplicateImports(source);

    // Install this engine's allocator as the active one and reset it.
    setActiveAllocator(this.allocator);
    this.allocator.reset();
    this.subst = new Substitution();
    this.diagnostics = [];
    this.nodeTypes = new Map();
    this.declaredSchemes = new Map();
    this.nodeTypesByEnd = new Map();
    this.localKindEqs = [];
    this.returnTypeOverrides = new Map();
    this.functionNodeTypes = new Map();
    this.methodSignatures = new Map();
    this.skolemDisplayNames = new Map();
    this.scopedTypeVars = new Map();
    this.rigidRowIds = new Set();
    this.skolemOrigins = new Map();
    this.enclosingAnnotatedReturns = [];
    this.importResolver = importResolver ?? null;
    this.typeDirectiveResolver = typeDirectiveResolver ?? null;
    this.importTypeAliasResolver = importTypeAliasResolver ?? null;
    this.exportedNames = new Set();
    this.cjsExportTypes = new Map();
    this.cjsValueExports = new Set();
    this.cjsObjectExportType = null;
    this.usesCjsExports = false;
    this.staticMemberTypes = new Map();
    this.pendingConstraints = [];
    this.fileReps = [];
    this.importedReps = [];
    this.pendingUnionConstraints = [];
    this.kvConstraints = new Map();
    this.rankNSkolemPromises = new Map();
    this.kvConstructorConstraints = new Map();
    this.constraintConstructorRewrites = [];
    this.defaultExportName = null;
    this.curryFunctionNames = new Set();
    this.curryNFunctionNames = new Map();
    this.optionalParamSlotsByDottedName = new Map();
    this.pendingIsCurriedResult = false;
    this.pendingConditionalReturn = null;
    this.curriedNodes = new Set();
    this.callSiteOverloadIndex = new Map();
    this.unboundIdentifiers = new Set();
    this.unconstrainedPropAccesses = new Set();
    this.deferredMemberAccesses = [];
    this.constructorProperties = new Set();
    this.privateClassMembers = new Map();
    this.constructorProvenance = new Map();
    this.constructorParentSumtype = new Map();
    this.builtinCtorKind = new Map();
    this.builtinCtorByVarName = new Map();
    this.frozenPropertyTypeStr = new Map();
    this.frozenParamType = new Map();
    this.suppressAutoUnion = false;
    this.generatorYieldStack = [];
    this.generatorFunctionNames = new Set();
    this.suppressInfiniteType = false;
    this.suppressPoisonDepth = 0;
    this.infiniteTypeSuppressedDuringAnnotation = false;
    this.currentBindingName = undefined;
    this.spreadChainPeel = new Map();
    this.defaultImportSources = new Map();

    // Clear custom method/constraint/data-type registrations from previous runs
    clearGlobalRegistries();

    // Process ::global directives from the project globals file (if provided).
    // Must run before the file's own directives so that file-level annotations
    // can override globals when needed.
    this.globalDirectiveMethods = [];
    if (this.globalsSource) {
      this.globalDirectiveMethods = processGlobalDirectives(this.globalsSource, () => {});
      // Also process ::constraint directives from the globals file
      processConstraintDirectives(this.globalsSource, () => {});
    }

    // Annotation & directive setup pass (→ setupPass.ts): annotation maps,
    // `::` directives, import pre-resolution, validation, constraint baking.
    setupFns.runAnnotationSetup(this, source);





    const currentEnv = env ?? defaultEnv();

    let ast: estree.Program;
    let parseErrorDiag: { message: string; start: number; end: number } | null = null;
    try {
      ast = parseStrict(source);
    } catch (e: unknown) {
      // The façade normalizes the parser's error object into a tightly-scoped
      // { message, start, end } so the editor underlines the exact problem
      // token rather than the whole file.
      const { message: cleanMsg, start, end } = describeParseError(e, source);
      // Try the loose parser so the rest of the file still type-checks and the
      // LSP keeps providing hover/completion/diagnostics for valid portions.
      try {
        ast = parseLoose(source);
        // Recovered: emit the syntax error WITHOUT the "Parse error:" prefix
        // so the LSP diagnostic filter (which suppresses noisy parse errors
        // while typing) doesn't hide it.  We also tighten the range to the
        // first identifier-like token at `start` so editors highlight the
        // offending name rather than the trailing `=`.
        let tightStart = start;
        let tightEnd = end;
        const idMatch = /^[A-Za-z_$][\w$]*/.exec(source.slice(start));
        if (idMatch) {
          tightEnd = start + idMatch[0].length;
        }
        parseErrorDiag = { message: cleanMsg, start: tightStart, end: tightEnd };
      } catch {
        return resultFns.buildResult(this, {
          type: tVoid,
          diagnostics: [{ message: `Parse error: ${cleanMsg}`, start, end }],
          exports: new Map(),
          topLevelBindings: new Map(),
        });
      }
    }

    let finalEnv: TypeEnv;
    let resultType: Type;
    try {
      [finalEnv, resultType] = this.inferProgramWithEnv(ast, currentEnv);

      // Collect top-level binding source ranges for the diagnostics service
      // (powers `trustAnnotations: 'all-bodies'` / `'annotated-bodies'`).
      // Done after inference so `this.annotationMap` is fully populated.
      this.bindingExtents = collectTopLevelBindingExtents(ast, this.annotationMap);

      // Validate pending constraints now that type variables are resolved
      exprMemberFns.flushDeferredMemberAccesses(this);
      this.validatePendingConstraints();
      this.validatePendingUnionConstraints();
      this.validateMissingConstraints();
    } catch (e: unknown) {
      // Catch-all so a single bad file never crashes the server
      const msg = e instanceof Error ? e.message : String(e);
      const diags: InferenceDiagnostic[] = [...this.diagnostics];
      if (parseErrorDiag) diags.unshift(parseErrorDiag);
      diags.push({ message: `Internal inference error: ${msg}`, start: 0, end: source.length });
      return resultFns.buildResult(this, {
        type: tVoid,
        diagnostics: diags,
        exports: new Map(),
        topLevelBindings: new Map(),
      });
    }

    // Build exports, top-level bindings, and post-process constraint rewrites
    const exportMap = resultFns.buildExportMap(this, finalEnv, currentEnv);
    setModuleReps(exportMap, [...this.fileReps, ...this.importedReps]);
    const topLevelBindings = resultFns.buildTopLevelBindings(this, finalEnv, currentEnv);
    resultFns.postProcessConstraintRewrites(this);
    resultFns.overrideSumtypeIdentifierTypes(this, source, topLevelBindings);

    const finalDiags = parseErrorDiag
      ? [parseErrorDiag, ...this.diagnostics]
      : this.diagnostics;

    return resultFns.buildResult(this, {
      type: this.subst.apply(resultType),
      diagnostics: finalDiags,
      exports: exportMap,
      topLevelBindings,
    });
  }

  // =======================================================================
  // infer() result helpers → results.ts
  // =======================================================================



  // =======================================================================
  // Statement delegates (→ statements.ts)
  // =======================================================================

  inferProgramWithEnv(program: estree.Program, env: TypeEnv): [TypeEnv, Type] {
    return stmtFns.inferProgramWithEnv(this, program, env);
  }

  inferStatement(node: AstNode, env: TypeEnv): [TypeEnv, Type] {
    return stmtFns.inferStatement(this, node, env);
  }

  inferVariableDeclaration(node: estree.VariableDeclaration, env: TypeEnv): [TypeEnv, Type] {
    return stmtFns.inferVariableDeclaration(this, node, env);
  }

  inferNamedBinding(name: string, decl: estree.VariableDeclarator, env: TypeEnv, nodeKind: string, parentStart?: number): { scheme: Scheme; displayType: Type } {
    return stmtFns.inferNamedBinding(this, name, decl, env, nodeKind, parentStart);
  }

  inferFunctionDeclaration(node: estree.FunctionDeclaration | estree.AnonymousFunctionDeclaration, env: TypeEnv): [TypeEnv, Type] {
    return stmtFns.inferFunctionDeclaration(this, node, env);
  }

  inferObjectDestructuring(decl: estree.VariableDeclarator, env: TypeEnv, kind: string): { env: TypeEnv; lastType: Type } {
    return stmtFns.inferObjectDestructuring(this, decl, env, kind);
  }

  inferDestructuringPattern(pattern: AstNode, sourceType: Type, env: TypeEnv, kind: string, freezeLeaves = false): { env: TypeEnv } {
    return stmtFns.inferDestructuringPattern(this, pattern, sourceType, env, kind, freezeLeaves);
  }

  inferWhileStatement(node: estree.WhileStatement, env: TypeEnv): [TypeEnv, Type] {
    return stmtFns.inferWhileStatement(this, node, env);
  }

  inferDoWhileStatement(node: estree.DoWhileStatement, env: TypeEnv): [TypeEnv, Type] {
    return stmtFns.inferDoWhileStatement(this, node, env);
  }

  inferForStatement(node: estree.ForStatement, env: TypeEnv): [TypeEnv, Type] {
    return stmtFns.inferForStatement(this, node, env);
  }

  inferForInStatement(node: estree.ForInStatement, env: TypeEnv): [TypeEnv, Type] {
    return stmtFns.inferForInStatement(this, node, env);
  }

  inferForOfStatement(node: estree.ForOfStatement, env: TypeEnv): [TypeEnv, Type] {
    return stmtFns.inferForOfStatement(this, node, env);
  }

  inferSwitchStatement(node: estree.SwitchStatement, env: TypeEnv): [TypeEnv, Type] {
    return stmtFns.inferSwitchStatement(this, node, env);
  }

  inferTryStatement(node: estree.TryStatement, env: TypeEnv): [TypeEnv, Type] {
    return stmtFns.inferTryStatement(this, node, env);
  }

  // =======================================================================
  // Expression delegates (→ expressions.ts)
  // =======================================================================

  inferExpression(node: AstNode, env: TypeEnv): Type {
    return exprFns.inferExpression(this, node, env);
  }

  inferExpressionWithExpected(node: AstNode, env: TypeEnv, expectedType: Type | undefined): Type {
    return exprFns.inferExpressionWithExpected(this, node, env, expectedType);
  }

  inferFunctionExpression(node: AstNode, env: TypeEnv, expectedType?: Type): Type {
    return exprFns.inferFunctionExpression(this, node as estree.Function, env, expectedType);
  }

  inferMemberExpression(node: estree.MemberExpression, env: TypeEnv): Type {
    return exprFns.inferMemberExpression(this, node, env);
  }

  tryInferPrototypeMethodAssignment(node: estree.AssignmentExpression, env: TypeEnv): Type | null {
    return exprFns.tryInferPrototypeMethodAssignment(this, node, env);
  }

  // =======================================================================
  // Call delegates (→ calls.ts)
  // =======================================================================

  inferCallExpression(node: estree.CallExpression, env: TypeEnv, expectedResultType?: Type): Type {
    const result = callFns.inferCallExpression(this, node, env, expectedResultType);
    // A call to a generator function (`function* f`) evaluates to a
    // `Generator <element>` value.  The function type itself carries the
    // element type as its result, so wrap that here at the call site.
    if (node.callee.type === 'Identifier'
        && this.generatorFunctionNames.has((node.callee as estree.Identifier).name)) {
      return tCon('Generator', [this.subst.apply(result)]);
    }
    return result;
  }

  /** Rank-N subsumption check of an expression against a `forall` type
   *  (delegates to calls.ts; also used for record-field construction). */
  inferRankNArgument(node: AstNode, env: TypeEnv, expected: Extract<Type, { tag: 'TForall' }>, rankNSkolems: Set<string>): Type {
    return callFns.inferRankNArgument(this, node, env, expected, rankNSkolems);
  }

  // =======================================================================
  // Module delegates (→ modules.ts)
  // =======================================================================

  inferImportDeclaration(node: estree.ImportDeclaration, env: TypeEnv): TypeEnv {
    return modFns.inferImportDeclaration(this, node, env);
  }

  inferExportNamedDeclaration(node: estree.ExportNamedDeclaration, env: TypeEnv): [TypeEnv, Type] {
    return modFns.inferExportNamedDeclaration(this, node, env);
  }

  inferExportDefaultDeclaration(node: estree.ExportDefaultDeclaration, env: TypeEnv): [TypeEnv, Type] {
    return modFns.inferExportDefaultDeclaration(this, node, env);
  }

  inferExportAllDeclaration(node: estree.ExportAllDeclaration, env: TypeEnv): [TypeEnv, Type] {
    return modFns.inferExportAllDeclaration(this, node, env);
  }

  inferClassDeclaration(node: estree.ClassDeclaration | estree.AnonymousClassDeclaration, env: TypeEnv): [TypeEnv, Type] {
    return modFns.inferClassDeclaration(this, node, env);
  }

  // -----------------------------------------------------------------------
  // Constraint-aware instantiation & validation
  // -----------------------------------------------------------------------

  /** Record a constraint on a kind-variable — see `src/infer/constraints.ts`. */
  private registerKvConstraint(varId: number, constraint: { className: string; isApplied?: boolean }, unique = false): void {
    constraintFns.registerKvConstraint(this, varId, constraint, unique);
  }

  /**
   * Instantiate a scheme and register pending constraint checks for any
   * constrained type variables — see `src/infer/constraints.ts`.
   */
  instantiateWithConstraints(scheme: Scheme, node: AstNode, annotation?: TypeAnnotation, skipPendingConstraints?: boolean, preBindings?: Map<string, Type>, asGiven?: boolean): Type {
    return constraintFns.instantiateWithConstraints(this, scheme, node, annotation, skipPendingConstraints, preBindings, asGiven);
  }

  /** Register constraint info for static method body parameter TVars — see `src/infer/constraints.ts`. */
  registerStaticMethodConstraints(scheme: Scheme, bodyType: Type): void {
    constraintFns.registerStaticMethodConstraints(this, scheme, bodyType);
  }

  /**
   * Count pending constraints whose variable has resolved (under the CURRENT
   * substitution) to a concrete type that does NOT satisfy the constraint.
   * Read-only mirror of {@link validatePendingConstraints} (emits no
   * diagnostics).  Used by overload selection to reject a branch that would
   * pin a constraint variable to an incompatible type (e.g. selecting the
   * `Category c => TypeRep c -> c` overload of `id` for `id(Function)` when
   * `Function` does not satisfy `Category`).
   */
  countViolatedPendingConstraints(): number {
    return constraintFns.countViolatedPendingConstraints(this);
  }

  /**
   * Report constraints that a callee REQUIRES on an enclosing function's own
   * (still-polymorphic) type variable but which the enclosing signature never
   * DECLARES.  Haskell's "No instance for (C a) arising from a use of …".
   *
   * Mechanism: an annotated constrained function body instantiates its OWN
   * signature as the authoritative expected type (`asGiven` → pending
   * constraints tagged `given`).  Callees referenced in the body push their
   * required constraints (wanted, `given` unset) onto vars that unify with the
   * enclosing function's declared type vars — so both givens and wanteds share
   * the same resolved var id (a bare TVar or a still-polymorphic `$kv:name:id`
   * higher-kinded TCon).  A wanted whose class is not entailed by the given
   * closure on that var (via `extends` superclasses) is an under-declared
   * constraint.  Only fires when the var carries at least one given, i.e. it
   * belongs to an annotated constrained function — never on inferred /
   * unconstrained polymorphic code.
   */
  validateMissingConstraints(): void {
    constraintFns.validateMissingConstraints(this);
  }

  /**
   * Validate all pending constraints after inference is complete.
   * Checks that each constrained type variable resolved to a concrete type
   * that satisfies the constraint (i.e., has all required methods registered).
   */
  validatePendingConstraints(): void {
    constraintFns.validatePendingConstraints(this);
  }

  /**
   * Validate pending structural-union constraints. Each constrained type
   * variable must unify with at least one of the listed alternatives.
   * The first alternative that successfully unifies wins; its substitution
   * is committed to the engine. If none unify, a diagnostic is emitted.
   * Variables still unresolved at this point are left alone (no diagnostic).
   */
  validatePendingUnionConstraints(): void {
    constraintFns.validatePendingUnionConstraints(this);
  }

  /**
   * Post-process a type by replacing constrained function types with their
   * constructor names.  E.g. replaces `a -> Identity a` with `Identity`
   * inside `EitherT e (a -> Identity a) String` → `EitherT e Identity String`.
   * Only rewrites nested occurrences (type args, function params/results,
   * record fields) — not the top-level type itself, so that a standalone
   * variable like `Identity :: a -> Identity a` keeps its function type.
   */
  applyConstraintConstructorRewrites(t: Type): Type {
    return constraintFns.applyConstraintConstructorRewrites(this, t);
  }

  // -----------------------------------------------------------------------
  // Utility
  // -----------------------------------------------------------------------

  /** Shorthand for pushing a diagnostic with a message and node location. */
  addDiag(message: string, loc: { start: number; end: number }, relatedInformation?: { message: string; start: number; end: number }[], severity?: number): void {
    const scrub = this.scrubSkolemStringDetailed(message);
    message = scrub.message;
    // When two distinct same-letter skolems collided in this message, point
    // the user at BOTH declaring annotations so "Cannot unify 'a' with 'a''"
    // is traceable to its two distinct `a`s.
    if (scrub.related.length > 0) {
      relatedInformation = [...(relatedInformation ?? []), ...scrub.related];
    }
    // De-dupe: identical message at the same span happens when several
    // unification call-sites (e.g. callee-type + result-type) all surface
    // the same root-cause error.
    for (const existing of this.diagnostics) {
      if (existing.message === message && existing.start === loc.start && existing.end === loc.end) {
        return;
      }
    }
    this.diagnostics.push({ message, start: loc.start, end: loc.end, relatedInformation, severity });
  }

  /** Record skolem→letter mappings minted while checking an annotated body.
   *  `origin` (the declaring annotation's name + comment range) enables the
   *  same-letter collision disambiguation in diagnostics. */
  registerSkolemNames(skolemToName: Map<string, string>, origin?: { name?: string; start: number; end: number }): void {
    for (const [k, v] of skolemToName) {
      this.skolemDisplayNames.set(k, v);
      if (origin && !this.skolemOrigins.has(k)) this.skolemOrigins.set(k, origin);
    }
  }

  /** Replace rigid skolem constants in a type with display vars carrying the
   *  annotation's letters, so hover never shows `§N`. */
  scrubForDisplay(t: Type): Type {
    return scrubSkolems(t, this.skolemDisplayNames);
  }

  /** Replace `§N` skolem tokens in a finished diagnostic string with the
   *  annotation's display letters (or `_` when unknown). */
  scrubSkolemString(message: string): string {
    return this.scrubSkolemStringDetailed(message).message;
  }

  /** Collision-aware skolem scrubbing.  Two DISTINCT skolems carrying the
   *  SAME letter (the `a` of a method annotation vs the `a` of the enclosing
   *  function's signature) would otherwise render an unreadable
   *  "Cannot unify 'a' with 'a'" — the second distinct skolem gets a prime
   *  suffix (`a'`), and each collided skolem with a known origin contributes
   *  a related-information entry pointing at its declaring annotation. */
  scrubSkolemStringDetailed(message: string): { message: string; related: { message: string; start: number; end: number }[] } {
    if (!message.includes(SKOLEM_PREFIX)) return { message, related: [] };
    const displayByToken = new Map<string, string>();
    const usedPerLetter = new Map<string, number>();
    const collidedTokens: string[] = [];
    const scrubbed = message.replace(/§\d+/g, tok => {
      let disp = displayByToken.get(tok);
      if (disp === undefined) {
        const letter = this.skolemDisplayNames.get(tok);
        if (letter === undefined) {
          disp = '_';
        } else {
          const n = usedPerLetter.get(letter) ?? 0;
          usedPerLetter.set(letter, n + 1);
          disp = n === 0 ? letter : letter + "'".repeat(n);
          if (n === 1) {
            // First collision on this letter: the token that claimed the
            // plain letter is also part of the collision — report it too.
            for (const [prevTok, prevDisp] of displayByToken) {
              if (prevDisp === letter) { collidedTokens.push(prevTok); break; }
            }
          }
          if (n >= 1) collidedTokens.push(tok);
        }
        displayByToken.set(tok, disp);
      }
      return disp;
    });
    const related: { message: string; start: number; end: number }[] = [];
    for (const tok of collidedTokens) {
      const origin = this.skolemOrigins.get(tok);
      if (!origin) continue;
      const disp = displayByToken.get(tok)!;
      const label = origin.name ? `'${origin.name}'` : 'this signature';
      related.push({
        message: `'${disp}' is a type variable of ${label}, declared here`,
        start: origin.start,
        end: origin.end,
      });
    }
    return { message: scrubbed, related };
  }

  /** Look up an annotation by name, falling back to offset-based method annotations. */
  lookupAnnotation(name: string | undefined, offset: number): TypeAnnotation | undefined {
    let annotation = name ? this.annotationMap.get(name) : undefined;
    // A same-named declaration elsewhere: use THIS declaration's annotation.
    if (annotation?.nodeStart !== undefined && annotation.nodeStart !== offset && name) {
      const own = this.annotationsByDeclaration.get(offset);
      if (own?.name === name) annotation = own;
    }
    if (!annotation) {
      const annByOffset = this.annotationByOffset.get(offset);
      if (annByOffset?.receiver && annByOffset?.methodType && annByOffset?.scheme
          && !annByOffset.methodNameMismatch) {
        annotation = annByOffset;
      }
    }
    return annotation;
  }

  /** Diagnostic-producing unification — see `src/infer/unifyDiag.ts`. */
  unifyWithDiagnostic(t1: Type, t2: Type, node: AstNode): void {
    unifyDiag.unifyWithDiagnostic(this, t1, t2, node);
  }

  /** Directional variant of `unifyWithDiagnostic` for the call-argument
   *  position — see `src/infer/unifyDiag.ts`. */
  unifyArgWithDiagnostic(argType: Type, paramType: Type, node: AstNode): void {
    unifyDiag.unifyArgWithDiagnostic(this, argType, paramType, node);
  }

  /** Shorthand for `checkAnnotationRigid` with bound engine state. */
  checkRigid(inferredType: Type, scheme: Scheme, node: AstNode): void {
    checkAnnotationRigid({ subst: this.subst, typeAliases: this.typeAliases, diagnostics: this.diagnostics, addDiag: this.boundAddDiag, aliasVars: this.typeAliasVars, skolemDisplayNames: this.skolemDisplayNames }, inferredType, scheme, node);
  }

  /** Expand a TCon alias if registered, instantiating any free alias vars
   *  with fresh TVars when the use-site provides no type arguments.  Used
   *  by call/array/array-elem code paths where the alias appears bare (e.g.
   *  `[Selector]` for `Selector :: (String | Prop a | QueryTag a | ...)`),
   *  so each occurrence binds its own fresh type variables. */
  maybeExpandAlias(t: Type): Type {
    if (t.tag !== 'TCon' || !this.typeAliases.has(t.name)) return t;
    const vars = this.typeAliasVars.get(t.name) ?? [];
    if (t.args.length === 0 && vars.length > 0) {
      const fresh = vars.map(() => tVar());
      const synthesized = { ...t, args: fresh };
      return expandAliases(this.typeAliases, synthesized, undefined, this.typeAliasVars);
    }
    if (t.args.length === 0) {
      return expandAliases(this.typeAliases, t, undefined, this.typeAliasVars);
    }
    return t;
  }

  /** Auto-union bridging on unification failure — see `src/infer/unifyDiag.ts`. */
  tryAutoUnion(t1: Type, r1: Type, t2: Type, r2: Type): boolean {
    return unifyDiag.tryAutoUnion(this, t1, r1, t2, r2);
  }

  /** TCon ↔ TFun bridging via instance-callable annotations — see `src/infer/unifyDiag.ts`. */
  tryConstructorCallable(t1: Type, r1: Type, t2: Type, r2: Type): boolean {
    return unifyDiag.tryConstructorCallable(this, t1, r1, t2, r2);
  }

  /** Deepest concretely-bound TVar in a substitution chain — see `src/infer/unifyDiag.ts`. */
  findRootTVarId(t: Type): number | null {
    return unifyDiag.findRootTVarId(this, t);
  }

  recordNodeType(node: AstNode, type: Type): void {
    // Record arrow/function nodes in a dedicated scope map (keyed by start,
    // keeping the smallest span) so hover can find the tightest enclosing
    // function even though the function's own entry in `nodeTypes` is
    // suppressed below in favour of its first parameter identifier.
    if (node.type === 'ArrowFunctionExpression' || node.type === 'FunctionExpression') {
      const prev = this.functionNodeTypes.get(node.start);
      const span = node.end - node.start;
      // Prefer the smallest span; on an equal span keep the LATEST recording so
      // a re-inferred function body (e.g. an overloaded callback resolved in a
      // later pass) overrides the stale variable ids captured by an earlier,
      // rolled-back trial.
      if (!prev || span <= (prev.end - node.start)) {
        this.functionNodeTypes.set(node.start, { type, end: node.end });
      }
    }
    // Always store by end offset for completion lookups (e.g. after call expressions).
    // Keep the most specific (smallest span) entry when multiple nodes share an end offset.
    // This is done before the early-return guards below so that CallExpression types
    // (which share the same start as their callee Identifier) are still captured.
    if (node.type !== 'ArrowFunctionExpression' && node.type !== 'FunctionExpression') {
      const existing = this.nodeTypesByEnd.get(node.end);
      const span = node.end - node.start;
      if (!existing || span < (node.end - existing.start)) {
        this.nodeTypesByEnd.set(node.end, { type, start: node.start });
      }
    }

    // For arrow/function expressions, don't overwrite a parameter already
    // recorded at this offset (the first param shares the same start).
    if (
      (node.type === 'ArrowFunctionExpression' || node.type === 'FunctionExpression') &&
      this.nodeTypes.has(node.start)
    ) {
      return;
    }
    // For compound expressions (MemberExpression, BinaryExpression, etc.)
    // that share the same start offset as a child Identifier, don't overwrite.
    // The Identifier type is more useful for hover since the cursor resolves
    // to the innermost node first.
    if (
      node.type !== 'Identifier' && node.type !== 'Literal' &&
      this.nodeTypes.has(node.start)
    ) {
      return;
    }
    this.nodeTypes.set(node.start, { type, end: node.end });
  }

  /** Lookup an inferred node type by AST node start offset.  Used by
   *  post-processing hooks (such as the `Picked` projection in
   *  `infer/calls.ts`) that need to inspect the resolved type of a
   *  sub-expression by AST identity.  Falls back to the by-end-offset
   *  map when no entry was recorded at the start offset (e.g. a
   *  CallExpression whose callee Identifier already claimed the start
   *  slot first via `recordNodeType`'s overlap guard). */
  getNodeType(node: AstNode): Type | undefined {
    const direct = this.nodeTypes.get(node.start)?.type;
    if (direct !== undefined) {
      // When the start-keyed entry actually belongs to a strictly smaller
      // span (i.e. a child node such as a callee Identifier), prefer the
      // end-keyed entry whose start matches this node exactly.
      const endEntry = this.nodeTypesByEnd.get(node.end);
      if (endEntry && endEntry.start === node.start) return endEntry.type;
      return direct;
    }
    return this.nodeTypesByEnd.get(node.end)?.type;
  }

  /**
   * Coordinately instantiate receiver + methodType from a method annotation,
   * ensuring both share the same fresh type variables.
   * Pre-condition: ann.scheme, ann.receiver, and ann.methodType must be defined.
   */
  coordinateInstantiate(ann: TypeAnnotation): { thisType: Type; expectedType: Type } {    const varNames = new Map<number, string>();
    collectVarNames(ann.receiver!, varNames);
    collectVarNames(ann.methodType!, varNames);

    // Row- and label-variables must be freshened as rows/labels (not plain
    // TVars) so open records like `{...a}` / `{a}` and label records keep
    // their open structure; otherwise the rest-row is lost and `{...a}`
    // collapses to the closed empty record `{}`.
    const labelIds = new Set<number>();
    collectLabelVarIds(ann.receiver!, labelIds);
    collectLabelVarIds(ann.methodType!, labelIds);
    const rowIds = new Set<number>();
    collectRowVarIds(ann.receiver!, rowIds);
    collectRowVarIds(ann.methodType!, rowIds);

    const freshSubst = new Substitution();
    const varIdMap = new Map<string, number>();
    for (const v of ann.scheme!.vars) {
      const name = varNames.get(v);
      if (labelIds.has(v)) {
        const fresh = tVar(name);
        freshSubst.set(v, { tag: 'TLabel', kind: 'var', id: fresh.id, name: name ?? fresh.name });
        if (name) varIdMap.set(name, fresh.id);
        continue;
      }
      if (rowIds.has(v)) {
        const freshRow = tRow(name);
        freshSubst.set(v, freshRow);
        if (name) varIdMap.set(name, freshRow.id);
        continue;
      }
      const fresh = tVar(name);
      freshSubst.set(v, fresh);
      if (name) varIdMap.set(name, fresh.id);
    }

    // Register constraints (e.g. Applicative f) for the fresh TVars
    if (ann.scheme!.constraints) {
      for (const constraint of ann.scheme!.constraints) {
        const freshId = varIdMap.get(constraint.typeVarName);
        if (freshId !== undefined) {
          this.registerKvConstraint(freshId, constraint);
        }
      }
    }

    return {
      thisType: freshSubst.apply(ann.receiver!),
      expectedType: freshSubst.apply(ann.methodType!),
    };
  }

  /**
   * Skolem variant of `coordinateInstantiate`: instantiate receiver +
   * methodType with rigid skolem constants (shared across both) instead of
   * fresh unifiable TVars.  Used when checking an annotated method body so the
   * body cannot poison the annotation's parameter / `this` / return display.
   * Also returns the skolem→name map so the rigid types can be scrubbed back
   * to the annotation's letters for hover display and diagnostics.
   */
  coordinateInstantiateSkolem(ann: TypeAnnotation, preBindings?: Map<number, Type>): { thisType: Type; expectedType: Type; skolemToName: Map<string, string> } {
    const { subst, skolemToName } = skolemSubstForScheme(ann.scheme!, ann.receiver!, ann.methodType!, preBindings);
    // Pre-bound receiver vars may resolve to the ENCLOSING signature's skolems
    // (see enclosingReceiverBindings in expr-functions.ts).  Carry their
    // display letters into this instantiation's map so the local scrub of the
    // method's own type (expr-functions.ts) knows them too.
    if (preBindings) {
      for (const bound of preBindings.values()) {
        eachType(bound, n => {
          if (n.tag === 'TCon' && n.name.startsWith(SKOLEM_PREFIX) && !skolemToName.has(n.name)) {
            const letter = this.skolemDisplayNames.get(n.name);
            if (letter) skolemToName.set(n.name, letter);
          }
        });
      }
    }
    return {
      thisType: subst.apply(ann.receiver!),
      expectedType: subst.apply(ann.methodType!),
      skolemToName,
    };
  }

  propagateCurryFlags(scheme: Scheme, localName: string, nodeStart: number): void {
    if (scheme.curryLeadingArgs) {
      this.curryNFunctionNames.set(localName, scheme.curryLeadingArgs);
    } else if (scheme.isCurryWrapper) {
      this.curryFunctionNames.add(localName);
    }
    // Propagate isCurriedResult so overload suggestions show on hover
    if (scheme.isCurriedResult) {
      this.curriedNodes.add(nodeStart);
    }
  }

  /** Shorthand: apply the current substitution to a type. */
  resolve(t: Type): Type {
    return this.subst.apply(t);
  }

}
