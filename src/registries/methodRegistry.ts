// ============================================================================
// Method Registry — built-in method signatures for container types
//
// Plain language: this is the checker's dictionary of "which methods does
// each type have, and what is each method's type?".  It ships pre-filled
// with the standard JavaScript methods (Array#map, String#slice, …) and is
// extended at analysis time with user-annotated methods (`Type#method ::`).
// When the engine sees `nums.map(…)`, it looks the method up here.
//
// Each entry maps (TypeConstructor, methodName) to a function that, given
// fresh type variables for the container's type arguments, produces the
// method's type.  This allows the inference engine to track how container
// types change through method chains like:
//
//   // :: [Number]
//   const nums = [1, 2, 3];
//   const strs = nums.map(n => String(n));  // inferred: [String]
//   const bools = strs.map(s => s.length > 0); // inferred: [Boolean]
// ============================================================================

import { Type, Scheme, tVar, tFun, tCon, tNumber, tString, tBool, tUndefined, tVoid, tTuple, tArray, tRecord, tUnion, tLabelVar, tAnyType, T_UNION, T_SPREAD_ARRAY, T_OBJECT } from '../hm/types';
import {
  buildDomMethodTables, setDomSettingsState, isDomStrictNulls,
  domHasAnyFallback, type DomSettings,
} from './domGlobals';
import { resetDefaultEnvCache } from '../hm/env';
import { parseTypeSignature } from '../hm/typeParser';
import type { TypeAnnotation } from '../commentParser';

// ---------------------------------------------------------------------------
// Method signature factory
// ---------------------------------------------------------------------------

/**
 * A factory function that creates a fresh method signature.
 * It receives the type arguments of the container instance
 * (e.g., for `Array<Number>`, it receives `[Number]`),
 * and returns the method's type.
 */
export type MethodFactory = (typeArgs: Type[]) => Type;

export interface MethodEntry {
  /** The `Type#method` annotation when it carries a `::narrow` directive.
   *  Stored on the entry so it travels with registry snapshots: narrowing
   *  through a method of an IMPORTED sumtype (`if (either.isLeft)` with
   *  `Either` from `require`) finds it here, not in the file-local map. */
  narrowAnnotation?: TypeAnnotation;
  /** Methods that exist only on named transformer INSTANCES of this base
   *  type (`FutureEither#matchWith` on `FutureT`): the factory picks the
   *  candidate whose receiver matches the value — see `registerOnInstanceBase`. */
  instanceCandidates?: { receiver: Type & { tag: 'TCon' }; methodType: Type; raw: string }[];
  /** Human-readable HM signature template (for hover display) */
  signature: string;
  /** Factory that produces a concrete method type given the container's type args */
  factory: MethodFactory;
  /** True when the method is a static/constructor-level method (e.g. Animal.create). */
  isStatic?: boolean;
  /** Optional scheme for static methods with constraints (e.g. Monad m => ...) */
  scheme?: Scheme;
  /** For constrained instance methods: ordered names of the receiver TCon's type variables. */
  receiverVarNames?: string[];
  /** When true, this entry should be omitted from completion lists.  It
   *  remains fully usable when the user types it explicitly. */
  hidden?: boolean;
  /** When true, this entry is private to the owning type: it can be
   *  accessed via `this.x` inside the class / its prototype methods, but
   *  outside access (`obj.x`) emits a diagnostic.  Implies `hidden`. */
  private?: boolean;
  /** For user-defined methods declared on a record receiver (`{…}#m`):
   *  the receiver record shape, the method's full type, and its scheme.
   *  Retained so the method can be resolved on *any* record form (`{}`,
   *  `{a}`, `{...a}`, `{[i]::a}`, `{x::T}`) — the receiver row is unified
   *  with the actual record at the call site to bind its fields. */
  recordReceiver?: Type;
  recordMethodType?: Type;
  recordScheme?: Scheme;
}

// ---------------------------------------------------------------------------
// Built-in method definitions
// ---------------------------------------------------------------------------

/** Extract element type from type args, defaulting to a fresh type variable. */
function elemVar(typeArgs: Type[], index = 0, name = 'a'): Type {
  return typeArgs[index] ?? tVar(name);
}

/** Standard JS array iterator callback: (element, index, array) -> R */
function arrayCallback(elem: Type, result: Type): Type {
  // Index and array are optional for the callback (see TCon.optionalFrom).
  return tFun({ ...tTuple([elem, tNumber, tArray(elem)]), optionalFrom: 1 } as Type, result);
}

/** Create a MethodEntry for a constant property (no arguments needed). */
function prop(type: Type, signature: string): MethodEntry {
  return { signature, factory: () => type };
}

/** Create a MethodEntry for a simple function (no type args needed). */
function fn(from: Type, to: Type, signature: string): MethodEntry {
  return { signature, factory: () => tFun(from, to) };
}

/**
 * `toString` is a METHOD, not a property: `x.toString()` / `n.toString(10)`.
 * Seeding it (or `valueOf`) as a bare `prop(String)` made the resolved type the
 * `String` value itself, so a call site `this.toString(10)` reported
 * "Type 'String' is not callable".  Model it as a function accepting an
 * optional radix/format argument so both `x.toString()` and `n.toString(10)`
 * type-check.
 */
function toStringMethod(): MethodEntry {
  return { signature: '(Number | Undefined) -> String', factory: () => tFun(opt(tNumber), tString) };
}

/**
 * `toLocaleString`/`toLocaleDateString`/`toLocaleTimeString`: an optional
 * locale (`"nl-BE"` or a list) and optional `Intl` options.
 */
function localeMethod(): MethodEntry {
  return {
    signature: '(String | [String] | Undefined, Object String Any | Undefined) -> String',
    factory: () => tFun(
      tTuple([opt(tUnion([tString, tArray(tString)])), opt(tCon('Object', [tString, tAnyType]))]),
      tString,
    ),
  };
}

/** `valueOf`-style nullary method returning `type`. */
function nullaryMethod(type: Type, sig: string): MethodEntry {
  return { signature: `() -> ${sig}`, factory: () => tFun(tVoid, type) };
}

/**
 * Wrap a type as an optional parameter slot: `T | Undefined`.
 *
 * Models JS methods whose trailing argument(s) may be omitted at the call
 * site — e.g. `Array#sort`'s comparator or `String#indexOf`'s `fromIndex`.
 * A trailing tuple slot (or a sole parameter) typed `T | Undefined` is treated
 * as optional by the call-arity check (`tupleSlotAcceptsUndefined` /
 * `typeAcceptsUndefined`), so both the short and the full call shape
 * type-check (same pattern already used by `slice` and `Promise#then`).
 */
function opt(t: Type): Type {
  return tCon(T_UNION, [t, tUndefined]);
}

/** Bulk-create identical entries for a list of method names. */
function bulk(names: string[], entry: MethodEntry): Record<string, MethodEntry> {
  const result: Record<string, MethodEntry> = {};
  for (const name of names) result[name] = entry;
  return result;
}

function reduceFactory(typeArgs: Type[]): Type {
  const a = elemVar(typeArgs), b = tVar('b');
  // The initial accumulator value is optional in JS — `arr.reduce(fn)` uses
  // the first element as the seed.  Model it as `b | Undefined` so both
  // `reduce(fn)` and `reduce(fn, init)` type-check.
  return tFun(tTuple([tFun(tTuple([b, a, tNumber, tArray(a)]), b), opt(b)]), b);
}

const arrayMethods: Record<string, MethodEntry> = {
  map: {
    signature: '((a, Number, [a]) -> b) -> [b]',
    factory: (typeArgs) => {
      const a = elemVar(typeArgs), b = tVar('b');
      return tFun(arrayCallback(a, b), tArray(b));
    },
  },
  // Predicates (`filter`, `find`, `some`, `every`, `findIndex`,
  // `findLast`, `findLastIndex`): JavaScript reads the callback's result as
  // truthy or falsy, so any result is accepted (TypeScript: `unknown`):
  // `bets.filter (b => b.won)` with `won :: Boolean | Null`.
  filter: {
    signature: '((a, Number, [a]) -> t) -> [a]',
    factory: (typeArgs) => {
      const a = elemVar(typeArgs);
      return tFun(arrayCallback(a, tVar('t')), tArray(a));
    },
  },
  reduce: {
    signature: '((b, a, Number, [a]) -> b, b | Undefined) -> b',
    factory: reduceFactory,
  },
  reduceRight: {
    signature: '((b, a, Number, [a]) -> b, b | Undefined) -> b',
    factory: reduceFactory,
  },
  // The callback's result is ignored at runtime, so any result is accepted
  // (like a `void` callback in TypeScript): `xs.forEach (x => out.push (x))`.
  forEach: {
    signature: '((a, Number, [a]) -> b) -> ()',
    factory: (typeArgs) => tFun(arrayCallback(elemVar(typeArgs), tVar('b')), tVoid),
  },
  find: {
    signature: '((a, Number, [a]) -> t) -> a',
    factory: (typeArgs) => {
      const a = elemVar(typeArgs);
      return tFun(arrayCallback(a, tVar('t')), a);
    },
  },
  some: {
    signature: '((a, Number, [a]) -> t) -> Boolean',
    factory: (typeArgs) => tFun(arrayCallback(elemVar(typeArgs), tVar('t')), tBool),
  },
  every: {
    signature: '((a, Number, [a]) -> t) -> Boolean',
    factory: (typeArgs) => tFun(arrayCallback(elemVar(typeArgs), tVar('t')), tBool),
  },
  flatMap: {
    signature: '((a, Number, [a]) -> [b]) -> [b]',
    factory: (typeArgs) => {
      const a = elemVar(typeArgs), b = tVar('b');
      return tFun(arrayCallback(a, tArray(b)), tArray(b));
    },
  },
  // `xs.concat (ys)` and `xs.concat (y)`: JavaScript appends a list's
  // elements or a single value (`[].concat (handler (response))` with a
  // handler that returns one action or a list).
  concat: {
    signature: '[a] ~> ([b] | b) -> [a | b]',
    factory: (typeArgs) => {
      const a = elemVar(typeArgs);
      const b = tVar('b');
      return tFun(tUnion([tArray(b), b]), tArray(tUnion([a, b])));
    },
  },
  includes: {
    signature: '(a, Number | Undefined) -> Boolean',
    factory: (typeArgs) => tFun(tTuple([elemVar(typeArgs), opt(tNumber)]), tBool),
  },
  indexOf: {
    signature: '(a, Number | Undefined) -> Number',
    factory: (typeArgs) => tFun(tTuple([elemVar(typeArgs), opt(tNumber)]), tNumber),
  },
  lastIndexOf: {
    signature: '(a, Number | Undefined) -> Number',
    factory: (typeArgs) => tFun(tTuple([elemVar(typeArgs), opt(tNumber)]), tNumber),
  },
  length: prop(tNumber, 'Number'),
  reverse: {
    signature: '[a]',
    factory: (typeArgs) => tArray(elemVar(typeArgs)),
  },
  slice: {
    // JS Array.prototype.slice accepts (), (begin) or (begin, end); `slice ()`
    // is the idiomatic shallow copy.  Both arguments are optional.
    signature: '(Number | Undefined, Number | Undefined) -> [a]',
    factory: (typeArgs) => tFun(
      tTuple([tCon(T_UNION, [tNumber, tUndefined]), tCon(T_UNION, [tNumber, tUndefined])]),
      tArray(elemVar(typeArgs)),
    ),
  },
  splice: {
    // JS Array.prototype.splice: only `start` is required; `deleteCount`
    // is optional, and items after it are inserted (same element type).
    // Overload set: only `start` (the optional-argument relaxation does not
    // apply inside an overload set), no items, or one to three items.
    signature: '(Number, Number | Undefined) -> [a]',
    factory: (typeArgs) => {
      const a = elemVar(typeArgs);
      return tUnion([
        tFun(tNumber, tArray(a)),
        tFun(tTuple([tNumber, opt(tNumber)]), tArray(a)),
        tFun(tTuple([tNumber, tNumber, a]), tArray(a)),
        tFun(tTuple([tNumber, tNumber, a, a]), tArray(a)),
        tFun(tTuple([tNumber, tNumber, a, a, a]), tArray(a)),
      ], { overloadSet: true });
    },
  },
  sort: {
    // The comparator is optional — `arr.sort()` sorts lexicographically.
    signature: '(((a, a) -> Number) | Undefined) -> [a]',
    factory: (typeArgs) => {
      const a = elemVar(typeArgs);
      return tFun(opt(tFun(tTuple([a, a]), tNumber)), tArray(a));
    },
  },
  fill: {
    // `arr.fill(value)` — `start` and `end` are optional.
    signature: '(a, Number | Undefined, Number | Undefined) -> [a]',
    factory: (typeArgs) => {
      const a = elemVar(typeArgs);
      return tFun(tTuple([a, opt(tNumber), opt(tNumber)]), tArray(a));
    },
  },
  copyWithin: {
    // `arr.copyWithin(target)` — `start` and `end` are optional.
    signature: '(Number, Number | Undefined, Number | Undefined) -> [a]',
    factory: (typeArgs) => tFun(tTuple([tNumber, opt(tNumber), opt(tNumber)]), tArray(elemVar(typeArgs))),
  },
  at: {
    signature: 'Number -> a',
    factory: (typeArgs) => tFun(tNumber, elemVar(typeArgs)),
  },
  push: {
    signature: 'a -> Number',
    factory: (typeArgs) => tFun(elemVar(typeArgs), tNumber),
  },
  // Real nullary methods (`() -> a`), not the property-style shorthand: on a
  // generic `[a]` the shorthand made `xs.pop ()` CALL the element type
  // (`a := () -> r`).
  pop: {
    signature: '() -> a',
    factory: (typeArgs) => tFun(tVoid, elemVar(typeArgs)),
  },
  shift: {
    signature: '() -> a',
    factory: (typeArgs) => tFun(tVoid, elemVar(typeArgs)),
  },
  unshift: {
    signature: 'a -> Number',
    factory: (typeArgs) => tFun(elemVar(typeArgs), tNumber),
  },
  findIndex: {
    signature: '((a, Number, [a]) -> t) -> Number',
    factory: (typeArgs) => tFun(arrayCallback(elemVar(typeArgs), tVar('t')), tNumber),
  },
  findLast: {
    signature: '((a, Number, [a]) -> t) -> a',
    factory: (typeArgs) => {
      const a = elemVar(typeArgs);
      return tFun(arrayCallback(a, tVar('t')), a);
    },
  },
  findLastIndex: {
    signature: '((a, Number, [a]) -> t) -> Number',
    factory: (typeArgs) => tFun(arrayCallback(elemVar(typeArgs), tVar('t')), tNumber),
  },
  flat: {
    signature: '[b]',
    factory: () => tArray(tVar('b')),
  },
  keys: {
    signature: '[Number]',
    factory: () => tArray(tNumber),
  },
  values: {
    signature: '[a]',
    factory: (typeArgs) => tArray(elemVar(typeArgs)),
  },
  entries: {
    signature: '[(Number, a)]',
    factory: (typeArgs) => tArray(tTuple([tNumber, elemVar(typeArgs)])),
  },
  join: {
    // `arr.join()` defaults the separator to ",".
    signature: '(String | Undefined) -> String',
    factory: () => tFun(opt(tString), tString),
  },
  toString: toStringMethod(),
  isArray: {
    signature: 'a -> Boolean',
    factory: () => tFun(tVar('a'), tBool),
    isStatic: true,
  },
  // `Array.from`: a list (also what `Map#values`/`Set#values`/`keys` return,
  // modelled as lists), a `Set`, a `Map` (its entries), a string (its
  // characters), and the map-form `Array.from (source, (item, index) => b)`,
  // including the array-like `{ length }` (items are Undefined).  Tried in
  // this order (overload set).
  from: {
    signature: '[a] -> [a]',
    factory: () => {
      const a = tVar('a');
      const b = tVar('b');
      const k = tVar('k');
      const v = tVar('v');
      const n = tVar('n');
      const m = tVar('m');
      return tUnion([
        tFun(tArray(a), tArray(a)),
        tFun(tCon('Set', [b]), tArray(b)),
        tFun(tCon('Map', [k, v]), tArray(tTuple([k, v]))),
        tFun(tString, tArray(tString)),
        tFun(tTuple([tArray(n), tFun(tTuple([n, tNumber]), m)]), tArray(m)),
        tFun(tTuple([tRecord({ length: tNumber }), tFun(tTuple([tUndefined, tNumber]), m)]), tArray(m)),
      ], { overloadSet: true });
    },
    isStatic: true,
  },
  of: {
    signature: 'a -> [a]',
    factory: () => {
      const a = tVar('a');
      return tFun(a, tArray(a));
    },
    isStatic: true,
  },
};

// ---------------------------------------------------------------------------
// String methods / properties
// ---------------------------------------------------------------------------

const stringMethods: Record<string, MethodEntry> = {
  length: prop(tNumber, 'Number'),
  charAt: {
    // `str.charAt()` defaults the index to 0.
    signature: '(Number | Undefined) -> String',
    factory: () => tFun(opt(tNumber), tString),
  },
  includes: {
    signature: '(String, Number | Undefined) -> Boolean',
    factory: () => tFun(tTuple([tString, opt(tNumber)]), tBool),
  },
  indexOf: {
    signature: '(String, Number | Undefined) -> Number',
    factory: () => tFun(tTuple([tString, opt(tNumber)]), tNumber),
  },
  lastIndexOf: {
    signature: '(String, Number | Undefined) -> Number',
    factory: () => tFun(tTuple([tString, opt(tNumber)]), tNumber),
  },
  // JS String.prototype.slice accepts (), (begin) or (begin, end).
  slice: {
    signature: '(Number | Undefined, Number | Undefined) -> String',
    factory: () => tFun(
      tTuple([tCon(T_UNION, [tNumber, tUndefined]), tCon(T_UNION, [tNumber, tUndefined])]),
      tString,
    ),
  },
  toUpperCase: prop(tString, 'String'),
  toLowerCase: prop(tString, 'String'),
  trim: prop(tString, 'String'),
  split: {
    // Both `separator` (a String or a RegExp) and `limit` are optional.
    signature: '(String | RegExp | Undefined, Number | Undefined) -> [String]',
    factory: () => tFun(
      tTuple([tCon(T_UNION, [tString, tCon('RegExp'), tUndefined]), opt(tNumber)]),
      tArray(tString),
    ),
  },
  startsWith: {
    signature: '(String, Number | Undefined) -> Boolean',
    factory: () => tFun(tTuple([tString, opt(tNumber)]), tBool),
  },
  endsWith: {
    signature: '(String, Number | Undefined) -> Boolean',
    factory: () => tFun(tTuple([tString, opt(tNumber)]), tBool),
  },
  replace: {
    signature: '(RegExp | String, String) -> String',
    factory: () => tFun(tTuple([tCon(T_UNION, [tCon('RegExp'), tString]), tString]), tString),
  },
  replaceAll: {
    signature: '(RegExp | String, String) -> String',
    factory: () => tFun(tTuple([tCon(T_UNION, [tCon('RegExp'), tString]), tString]), tString),
  },
  concat: fn(tString, tString, 'String -> String'),
  at: fn(tNumber, tString, 'Number -> String'),
  padStart: {
    // `padString` is optional (defaults to " ").
    signature: '(Number, String | Undefined) -> String',
    factory: () => tFun(tTuple([tNumber, opt(tString)]), tString),
  },
  padEnd: {
    signature: '(Number, String | Undefined) -> String',
    factory: () => tFun(tTuple([tNumber, opt(tString)]), tString),
  },
  repeat: fn(tNumber, tString, 'Number -> String'),
  normalize: {
    // The Unicode normalization form is optional (defaults to "NFC").
    signature: '(String | Undefined) -> String',
    factory: () => tFun(opt(tString), tString),
  },
  match: fn(tCon('RegExp'), tArray(tString), 'RegExp -> [String]'),
  matchAll: fn(tCon('RegExp'), tArray(tArray(tString)), 'RegExp -> [[String]]'),
  search: fn(tCon('RegExp'), tNumber, 'RegExp -> Number'),
  codePointAt: fn(tNumber, tNumber, 'Number -> Number'),
  charCodeAt: fn(tNumber, tNumber, 'Number -> Number'),
  localeCompare: fn(tString, tNumber, 'String -> Number'),
  substring: {
    signature: '(Number, Number | Undefined) -> String',
    factory: () => tFun(
      tTuple([tNumber, tCon(T_UNION, [tNumber, tUndefined])]),
      tString,
    ),
  },
  substr: {
    signature: '(Number, Number | Undefined) -> String',
    factory: () => tFun(
      tTuple([tNumber, tCon(T_UNION, [tNumber, tUndefined])]),
      tString,
    ),
  },
  trimStart: prop(tString, 'String'),
  trimEnd: prop(tString, 'String'),
  toString: toStringMethod(),
  valueOf: nullaryMethod(tString, 'String'),
  // Statics
  fromCharCode: {
    signature: 'Number -> String',
    factory: () => tFun(tNumber, tString),
    isStatic: true,
  },
  fromCodePoint: {
    signature: 'Number -> String',
    factory: () => tFun(tNumber, tString),
    isStatic: true,
  },
  raw: {
    signature: 'a -> String',
    factory: () => tFun(tVar('a'), tString),
    isStatic: true,
  },
};

// ---------------------------------------------------------------------------
// Promise methods
// ---------------------------------------------------------------------------

const promiseMethods: Record<string, MethodEntry> = {
  // then :: Promise e a ~> (a -> b, (e -> c) | Undefined) -> Promise e (Awaited b)
  // Supports 1-arg (onFulfilled) and 2-arg (onFulfilled, onRejected) forms.
  // `Awaited b` (reduced after the call, see `applyAwaitedReduction`)
  // flattens a callback that returns a Promise, as at runtime:
  // `p.then (() => fetchUser (id))` is a `Promise e User`.
  then: {
    signature: '(a -> b, (e -> c) | Undefined) -> Promise e (Awaited b)',
    factory: (typeArgs: Type[]) => {
      const e = elemVar(typeArgs, 0, 'e');
      const a = elemVar(typeArgs, 1, 'a');
      const b = tVar('b');
      const c = tVar('c');
      return tFun(
        tTuple([tFun(a, b), tCon(T_UNION, [tFun(e, c), tUndefined])]),
        tCon('Promise', [e, tCon('Awaited', [b])]),
      );
    },
  },

  // catch :: Promise e a ~> (e -> b) -> Promise e b
  catch: {
    signature: '(e -> b) -> Promise e b',
    factory: (typeArgs: Type[]) => {
      const e = elemVar(typeArgs, 0, 'e');
      const b = tVar('b');
      return tFun(tFun(e, b), tCon('Promise', [e, b]));
    },
  },

  // finally :: Promise e a ~> (() -> ()) -> Promise e a
  finally: {
    signature: '(() -> ()) -> Promise e a',
    factory: (typeArgs: Type[]) => {
      const e = elemVar(typeArgs, 0, 'e');
      const a = elemVar(typeArgs, 1, 'a');
      return tFun(tFun(tVoid, tVoid), tCon('Promise', [e, a]));
    },
  },

  // ---- Statics ----
  resolve: {
    signature: 'a -> Promise e a',
    factory: () => {
      const a = tVar('a');
      const e = tVar('e');
      return tFun(a, tCon('Promise', [e, a]));
    },
    isStatic: true,
  },
  reject: {
    signature: 'e -> Promise e a',
    factory: () => {
      const e = tVar('e');
      const a = tVar('a');
      return tFun(e, tCon('Promise', [e, a]));
    },
    isStatic: true,
  },
  all: {
    signature: '[Promise e a] -> Promise e [a]',
    factory: () => {
      const a = tVar('a');
      const e = tVar('e');
      return tFun(tArray(tCon('Promise', [e, a])), tCon('Promise', [e, tArray(a)]));
    },
    isStatic: true,
  },
  race: {
    signature: '[Promise e a] -> Promise e a',
    factory: () => {
      const a = tVar('a');
      const e = tVar('e');
      return tFun(tArray(tCon('Promise', [e, a])), tCon('Promise', [e, a]));
    },
    isStatic: true,
  },
  allSettled: {
    signature: '[Promise e a] -> Promise e [a]',
    factory: () => {
      const a = tVar('a');
      const e = tVar('e');
      return tFun(tArray(tCon('Promise', [e, a])), tCon('Promise', [e, tArray(a)]));
    },
    isStatic: true,
  },
  any: {
    signature: '[Promise e a] -> Promise e a',
    factory: () => {
      const a = tVar('a');
      const e = tVar('e');
      return tFun(tArray(tCon('Promise', [e, a])), tCon('Promise', [e, a]));
    },
    isStatic: true,
  },
};

// ---------------------------------------------------------------------------
// Map methods
// ---------------------------------------------------------------------------

const mapMethods: Record<string, MethodEntry> = {
  // A missing key gives `undefined`: narrow the result (`== null`, a guard)
  // or annotate the binding (`// rate :: Number` above `const rate =
  // rates.get (code)`) when the key is known to be present.
  get: {
    signature: 'k -> (v | Undefined)',
    factory: (typeArgs: Type[]) => {
      const k = elemVar(typeArgs, 0, 'k');
      const v = elemVar(typeArgs, 1, 'v');
      return tFun(k, tUnion([v, tUndefined]));
    },
  },
  set: {
    signature: '(k, v) -> Map k v',
    factory: (typeArgs: Type[]) => {
      const k = elemVar(typeArgs, 0, 'k');
      const v = elemVar(typeArgs, 1, 'v');
      return tFun(tTuple([k, v]), tCon('Map', [k, v]));
    },
  },
  has: {
    signature: 'k -> Boolean',
    factory: (typeArgs: Type[]) => {
      const k = elemVar(typeArgs, 0, 'k');
      return tFun(k, tBool);
    },
  },
  delete: {
    signature: 'k -> Boolean',
    factory: (typeArgs: Type[]) => {
      const k = elemVar(typeArgs, 0, 'k');
      return tFun(k, tBool);
    },
  },
  clear: prop(tVoid, 'Void'),
  size: prop(tNumber, 'Number'),
  forEach: {
    signature: '((v, k, Map k v) -> b) -> ()',
    factory: (typeArgs: Type[]) => {
      const k = elemVar(typeArgs, 0, 'k');
      const v = elemVar(typeArgs, 1, 'v');
      return tFun(tFun(tTuple([v, k, tCon('Map', [k, v])]), tVar('b')), tVoid);
    },
  },
  keys: {
    signature: '[k]',
    factory: (typeArgs: Type[]) => {
      const k = elemVar(typeArgs, 0, 'k');
      return tArray(k);
    },
  },
  values: {
    signature: '[v]',
    factory: (typeArgs: Type[]) => {
      const v = elemVar(typeArgs, 1, 'v');
      return tArray(v);
    },
  },
  entries: {
    signature: '[(k, v)]',
    factory: (typeArgs: Type[]) => {
      const k = elemVar(typeArgs, 0, 'k');
      const v = elemVar(typeArgs, 1, 'v');
      return tArray(tTuple([k, v]));
    },
  },
  groupBy: {
    signature: '([a], (a -> k)) -> Map k [a]',
    factory: () => {
      const a = tVar('a');
      const k = tVar('k');
      return tFun(tTuple([tArray(a), tFun(a, k)]), tCon('Map', [k, tArray(a)]));
    },
    isStatic: true,
  },
};
// ---------------------------------------------------------------------------

const setMethods: Record<string, MethodEntry> = {
  add: {
    signature: 'a -> Set a',
    factory: (typeArgs: Type[]) => {
      const a = elemVar(typeArgs);
      return tFun(a, tCon('Set', [a]));
    },
  },
  has: {
    signature: 'a -> Boolean',
    factory: (typeArgs: Type[]) => {
      const a = elemVar(typeArgs);
      return tFun(a, tBool);
    },
  },
  delete: {
    signature: 'a -> Boolean',
    factory: (typeArgs: Type[]) => {
      const a = elemVar(typeArgs);
      return tFun(a, tBool);
    },
  },
  clear: prop(tVoid, 'Void'),
  size: prop(tNumber, 'Number'),
  forEach: {
    signature: '((a, a, Set a) -> b) -> ()',
    factory: (typeArgs: Type[]) => {
      const a = elemVar(typeArgs);
      return tFun(tFun(tTuple([a, a, tCon('Set', [a])]), tVar('b')), tVoid);
    },
  },
  values: {
    signature: '[a]',
    factory: (typeArgs: Type[]) => {
      const a = elemVar(typeArgs);
      return tArray(a);
    },
  },
  keys: {
    signature: '[a]',
    factory: (typeArgs: Type[]) => tArray(elemVar(typeArgs)),
  },
  entries: {
    signature: '[(a, a)]',
    factory: (typeArgs: Type[]) => {
      const a = elemVar(typeArgs);
      return tArray(tTuple([a, a]));
    },
  },
  union: {
    signature: 'Set a -> Set a',
    factory: (typeArgs: Type[]) => {
      const a = elemVar(typeArgs);
      return tFun(tCon('Set', [a]), tCon('Set', [a]));
    },
  },
  intersection: {
    signature: 'Set a -> Set a',
    factory: (typeArgs: Type[]) => {
      const a = elemVar(typeArgs);
      return tFun(tCon('Set', [a]), tCon('Set', [a]));
    },
  },
  difference: {
    signature: 'Set a -> Set a',
    factory: (typeArgs: Type[]) => {
      const a = elemVar(typeArgs);
      return tFun(tCon('Set', [a]), tCon('Set', [a]));
    },
  },
  symmetricDifference: {
    signature: 'Set a -> Set a',
    factory: (typeArgs: Type[]) => {
      const a = elemVar(typeArgs);
      return tFun(tCon('Set', [a]), tCon('Set', [a]));
    },
  },
  isSubsetOf: {
    signature: 'Set a -> Boolean',
    factory: (typeArgs: Type[]) => tFun(tCon('Set', [elemVar(typeArgs)]), tBool),
  },
  isSupersetOf: {
    signature: 'Set a -> Boolean',
    factory: (typeArgs: Type[]) => tFun(tCon('Set', [elemVar(typeArgs)]), tBool),
  },
  isDisjointFrom: {
    signature: 'Set a -> Boolean',
    factory: (typeArgs: Type[]) => tFun(tCon('Set', [elemVar(typeArgs)]), tBool),
  },
};
// ---------------------------------------------------------------------------

const regexpMethods: Record<string, MethodEntry> = {
  test: fn(tString, tBool, 'String -> Boolean'),
  exec: fn(tString, tArray(tString), 'String -> [String]'),
  source: prop(tString, 'String'),
  flags: prop(tString, 'String'),
  global: prop(tBool, 'Boolean'),
  ignoreCase: prop(tBool, 'Boolean'),
  multiline: prop(tBool, 'Boolean'),
  sticky: prop(tBool, 'Boolean'),
  unicode: prop(tBool, 'Boolean'),
  dotAll: prop(tBool, 'Boolean'),
  hasIndices: prop(tBool, 'Boolean'),
  lastIndex: prop(tNumber, 'Number'),
  toString: toStringMethod(),
};

// ---------------------------------------------------------------------------
// Number methods / properties
// ---------------------------------------------------------------------------

const numberMethods: Record<string, MethodEntry> = {
  toString: toStringMethod(),
  toFixed: fn(tNumber, tString, 'Number -> String'),
  toPrecision: fn(tNumber, tString, 'Number -> String'),
  toExponential: fn(tNumber, tString, 'Number -> String'),
  toLocaleString: localeMethod(),
  valueOf: nullaryMethod(tNumber, 'Number'),
  // Statics
  isInteger: {
    signature: 'a -> Boolean',
    factory: () => tFun(tVar('a'), tBool),
    isStatic: true,
  },
  isFinite: {
    signature: 'a -> Boolean',
    factory: () => tFun(tVar('a'), tBool),
    isStatic: true,
  },
  isNaN: {
    signature: 'a -> Boolean',
    factory: () => tFun(tVar('a'), tBool),
    isStatic: true,
  },
  isSafeInteger: {
    signature: 'a -> Boolean',
    factory: () => tFun(tVar('a'), tBool),
    isStatic: true,
  },
  parseInt: {
    signature: 'String -> Number',
    factory: () => tFun(tString, tNumber),
    isStatic: true,
  },
  parseFloat: {
    signature: 'String -> Number',
    factory: () => tFun(tString, tNumber),
    isStatic: true,
  },
  ...bulk(
    ['MAX_SAFE_INTEGER', 'MIN_SAFE_INTEGER', 'MAX_VALUE', 'MIN_VALUE',
     'EPSILON', 'POSITIVE_INFINITY', 'NEGATIVE_INFINITY', 'NaN'],
    { signature: 'Number', factory: () => tNumber, isStatic: true },
  ),
};

// ---------------------------------------------------------------------------
// Boolean methods
// ---------------------------------------------------------------------------

const booleanMethods: Record<string, MethodEntry> = {
  toString: toStringMethod(),
  valueOf: nullaryMethod(tBool, 'Boolean'),
};

// ---------------------------------------------------------------------------
// Error methods
// ---------------------------------------------------------------------------

const errorMethods: Record<string, MethodEntry> = {
  message: prop(tString, 'String'),
  name: prop(tString, 'String'),
  stack: prop(tString, 'String'),
  // Node system errors and most drivers carry a string `code` (`ENOENT`, a
  // PostgreSQL SQLSTATE such as `23503`, …); absent on plain errors.
  code: prop(opt(tString), 'String | Undefined'),
  cause: {
    signature: 'a',
    factory: () => tVar('a'),
  },
  toString: toStringMethod(),
};

// ---------------------------------------------------------------------------
// Function methods / properties
// ---------------------------------------------------------------------------

const functionMethods: Record<string, MethodEntry> = {
  length: prop(tNumber, 'Number'),
  name: prop(tString, 'String'),
  bind: {
    signature: 'a -> Function',
    factory: () => tFun(tVar('a'), tCon('Function', [])),
  },
  call: {
    signature: 'a -> b',
    factory: () => tFun(tVar('a'), tVar('b')),
  },
  apply: {
    signature: 'a -> b',
    factory: () => tFun(tVar('a'), tVar('b')),
  },
};

// ---------------------------------------------------------------------------
// Math methods / properties (static — accessed via Math.xxx)
// ---------------------------------------------------------------------------

const mathMethods: Record<string, MethodEntry> = {
  random: {
    signature: '() -> Number',
    factory: () => tFun(tVoid, tNumber),
    isStatic: true,
  },
  ...bulk(
    ['floor', 'ceil', 'round', 'abs', 'sqrt', 'cbrt', 'sign', 'trunc',
     'log', 'log2', 'log10', 'log1p', 'exp', 'expm1', 'sin', 'cos', 'tan', 'asin', 'acos', 'atan',
     'sinh', 'cosh', 'tanh', 'asinh', 'acosh', 'atanh', 'fround', 'clz32'],
    { signature: 'Number -> Number', factory: () => tFun(tNumber, tNumber), isStatic: true },
  ),
  ...bulk(
    ['atan2', 'pow', 'max', 'min', 'hypot', 'imul'],
    { signature: '(Number, Number) -> Number', factory: () => tFun(tTuple([tNumber, tNumber]), tNumber), isStatic: true },
  ),
  ...bulk(
    ['PI', 'E', 'LN2', 'LN10', 'LOG2E', 'LOG10E', 'SQRT2', 'SQRT1_2'],
    { signature: 'Number', factory: () => tNumber, isStatic: true },
  ),
};

// ---------------------------------------------------------------------------
// Object methods (all static)
// ---------------------------------------------------------------------------

const objectMethods: Record<string, MethodEntry> = {
  create: {
    signature: 'a -> a',
    factory: () => { const a = tVar('a'); return tFun(a, a); },
    isStatic: true,
  },
  keys: {
    signature: 'a -> [String]',
    factory: () => tFun(tVar('a'), tArray(tString)),
    isStatic: true,
  },
  values: {
    signature: 'a -> [b]',
    factory: () => tFun(tVar('a'), tArray(tVar('b'))),
    isStatic: true,
  },
  entries: {
    signature: 'a -> [[b]]',
    factory: () => tFun(tVar('a'), tArray(tArray(tVar('b')))),
    isStatic: true,
  },
  fromEntries: {
    signature: '[[b]] -> a',
    factory: () => tFun(tArray(tArray(tVar('b'))), tVar('a')),
    isStatic: true,
  },
  // Object.assign (target, ...sources) returns the target with every source
  // merged in (was `a -> a`, which dropped the sources' fields:
  // `Object.assign ({}, acc, item)` in an FP library's validateSpec).  One branch per
  // source count; record spread models the left-to-right overwrite.
  assign: {
    signature: '(a) -> a | (a, b) -> { ...a, ...b } | (a, b, c) -> { ...a, ...b, ...c } | (a, b, c, d) -> { ...a, ...b, ...c, ...d }',
    factory: () => tUnion([
      tFun(tVar('a'), tVar('a')),
      parseTypeSignature('(a, b) -> { ...a, ...b }').type,
      parseTypeSignature('(a, b, c) -> { ...a, ...b, ...c }').type,
      parseTypeSignature('(a, b, c, d) -> { ...a, ...b, ...c, ...d }').type,
    ]),
    isStatic: true,
  },
  freeze: {
    signature: 'a -> a',
    factory: () => { const a = tVar('a'); return tFun(a, a); },
    isStatic: true,
  },
  isFrozen: {
    signature: 'a -> Boolean',
    factory: () => tFun(tVar('a'), tBool),
    isStatic: true,
  },
  seal: {
    signature: 'a -> a',
    factory: () => { const a = tVar('a'); return tFun(a, a); },
    isStatic: true,
  },
  isSealed: {
    signature: 'a -> Boolean',
    factory: () => tFun(tVar('a'), tBool),
    isStatic: true,
  },
  is: {
    signature: '(a, a) -> Boolean',
    factory: () => { const a = tVar('a'); return tFun(tTuple([a, a]), tBool); },
    isStatic: true,
  },
  hasOwn: {
    signature: '(a, String) -> Boolean',
    factory: () => tFun(tTuple([tVar('a'), tString]), tBool),
    isStatic: true,
  },
  defineProperty: {
    signature: '(a, String, b) -> a',
    factory: () => { const a = tVar('a'); return tFun(tTuple([a, tString, tVar('b')]), a); },
    isStatic: true,
  },
  defineProperties: {
    signature: '(a, b) -> a',
    factory: () => { const a = tVar('a'); return tFun(tTuple([a, tVar('b')]), a); },
    isStatic: true,
  },
  getOwnPropertyNames: {
    signature: 'a -> [String]',
    factory: () => tFun(tVar('a'), tArray(tString)),
    isStatic: true,
  },
  getOwnPropertySymbols: {
    signature: 'a -> [Symbol]',
    factory: () => tFun(tVar('a'), tArray(tCon('Symbol'))),
    isStatic: true,
  },
  getOwnPropertyDescriptor: {
    signature: '(a, String) -> b',
    factory: () => tFun(tTuple([tVar('a'), tString]), tVar('b')),
    isStatic: true,
  },
  getOwnPropertyDescriptors: {
    signature: 'a -> b',
    factory: () => tFun(tVar('a'), tVar('b')),
    isStatic: true,
  },
  getPrototypeOf: {
    signature: 'a -> b',
    factory: () => tFun(tVar('a'), tVar('b')),
    isStatic: true,
  },
  setPrototypeOf: {
    signature: '(a, b) -> a',
    factory: () => { const a = tVar('a'); return tFun(tTuple([a, tVar('b')]), a); },
    isStatic: true,
  },
  preventExtensions: {
    signature: 'a -> a',
    factory: () => { const a = tVar('a'); return tFun(a, a); },
    isStatic: true,
  },
  isExtensible: {
    signature: 'a -> Boolean',
    factory: () => tFun(tVar('a'), tBool),
    isStatic: true,
  },
};

// ---------------------------------------------------------------------------
// JSON methods (all static)
// ---------------------------------------------------------------------------

const jsonMethods: Record<string, MethodEntry> = {
  parse: {
    signature: 'String -> a',
    factory: () => tFun(tString, tVar('a')),
    isStatic: true,
  },
  stringify: {
    signature: 'a -> String',
    factory: () => tFun(tVar('a'), tString),
    isStatic: true,
  },
};

// ---------------------------------------------------------------------------
// Date methods
// ---------------------------------------------------------------------------

const dateMethods: Record<string, MethodEntry> = {
  // Statics
  now: {
    signature: '() -> Number',
    factory: () => tFun(tVoid, tNumber),
    isStatic: true,
  },
  parse: {
    signature: 'String -> Number',
    factory: () => tFun(tString, tNumber),
    isStatic: true,
  },
  // Date.UTC (year, monthIndex, day?, hours?, minutes?, seconds?, ms?)
  UTC: {
    signature: '(Number, Number, Number | Undefined, Number | Undefined, Number | Undefined, Number | Undefined, Number | Undefined) -> Number',
    factory: () => tFun(tTuple([tNumber, tNumber, opt(tNumber), opt(tNumber), opt(tNumber), opt(tNumber), opt(tNumber)]), tNumber),
    isStatic: true,
  },
  // Instance getters
  ...bulk(
    ['getTime', 'getFullYear', 'getMonth', 'getDate', 'getDay',
     'getHours', 'getMinutes', 'getSeconds', 'getMilliseconds',
     'getTimezoneOffset',
     'getUTCFullYear', 'getUTCMonth', 'getUTCDate', 'getUTCDay',
     'getUTCHours', 'getUTCMinutes', 'getUTCSeconds', 'getUTCMilliseconds'],
    { signature: '() -> Number', factory: () => tFun(tVoid, tNumber) },
  ),
  // Instance setters
  ...bulk(
    ['setTime', 'setFullYear', 'setMonth', 'setDate',
     'setHours', 'setMinutes', 'setSeconds', 'setMilliseconds',
     'setUTCFullYear', 'setUTCMonth', 'setUTCDate',
     'setUTCHours', 'setUTCMinutes', 'setUTCSeconds', 'setUTCMilliseconds'],
    { signature: 'Number -> Number', factory: () => tFun(tNumber, tNumber) },
  ),
  // String conversions
  ...bulk(
    ['toISOString', 'toString', 'toJSON', 'toDateString', 'toTimeString', 'toUTCString'],
    { signature: '() -> String', factory: () => tFun(tVoid, tString) },
  ),
  toLocaleString: localeMethod(),
  toLocaleDateString: localeMethod(),
  toLocaleTimeString: localeMethod(),
  valueOf: nullaryMethod(tNumber, 'Number'),
};

// ---------------------------------------------------------------------------
// Symbol methods
// ---------------------------------------------------------------------------

const symbolMethods: Record<string, MethodEntry> = {
  // Statics
  for: {
    signature: 'String -> Symbol',
    factory: () => tFun(tString, tCon('Symbol')),
    isStatic: true,
  },
  keyFor: {
    signature: 'Symbol -> String',
    factory: () => tFun(tCon('Symbol'), tString),
    isStatic: true,
  },
  // Well-known symbol constants
  ...bulk(
    ['iterator', 'asyncIterator', 'hasInstance', 'isConcatSpreadable',
     'match', 'matchAll', 'replace', 'search', 'species', 'split',
     'toPrimitive', 'toStringTag', 'unscopables'],
    { signature: 'Symbol', factory: () => tCon('Symbol'), isStatic: true },
  ),
  // Instance
  description: prop(tString, 'String'),
  toString: toStringMethod(),
};

// ---------------------------------------------------------------------------
// BigInt methods
// ---------------------------------------------------------------------------

const bigintMethods: Record<string, MethodEntry> = {
  asIntN: {
    signature: '(Number, BigInt) -> BigInt',
    factory: () => tFun(tTuple([tNumber, tCon('BigInt')]), tCon('BigInt')),
    isStatic: true,
  },
  asUintN: {
    signature: '(Number, BigInt) -> BigInt',
    factory: () => tFun(tTuple([tNumber, tCon('BigInt')]), tCon('BigInt')),
    isStatic: true,
  },
  toString: toStringMethod(),
  toLocaleString: localeMethod(),
  valueOf: nullaryMethod(tCon('BigInt'), 'BigInt'),
};

// ---------------------------------------------------------------------------
// Console methods (all instance on the `console` singleton TCon('Console'))
// ---------------------------------------------------------------------------

const consoleMethods: Record<string, MethodEntry> = {
  ...bulk(
    ['log', 'info', 'warn', 'error', 'debug', 'trace', 'dir', 'table',
     'group', 'groupCollapsed', 'count', 'countReset', 'assert',
     'time', 'timeEnd', 'timeLog'],
    { signature: 'a -> ()', factory: () => tFun(tVar('a'), tVoid) },
  ),
  ...bulk(
    ['groupEnd', 'clear'],
    { signature: '() -> ()', factory: () => tFun(tVoid, tVoid) },
  ),
};

// ---------------------------------------------------------------------------
// Node.js `process` global — instance methods/properties on TCon('Process')
// ---------------------------------------------------------------------------

const processVersionsRecord = tRecord({
  node: tString,
  v8: tString,
  modules: tString,
  uv: tString,
  zlib: tString,
  ares: tString,
  openssl: tString,
});

// `process.stdout` / `process.stderr`: the writable-stream surface scripts use.
const processStreamRecord = (): Type => tRecord({
  write: tFun(tString, tBool),
  isTTY: opt(tBool),
});
const PROCESS_STREAM_SIG = '{ write :: String -> Boolean, isTTY :: Boolean | Undefined }';

const processMemoryUsageRecord = tRecord({
  rss: tNumber,
  heapTotal: tNumber,
  heapUsed: tNumber,
  external: tNumber,
  arrayBuffers: tNumber,
});

// ---------------------------------------------------------------------------
// `performance` global (Web + Node High Resolution Time) — TCon('Performance')
// ---------------------------------------------------------------------------

const performanceMethods: Record<string, MethodEntry> = {
  now:        fn(tVoid, tNumber, '() -> Number'),
  timeOrigin: prop(tNumber, 'Number'),
};

// ---------------------------------------------------------------------------
// `Intl` namespace (ECMA-402) — TCon('Intl').  The two formatters in common
// use; options are open dictionaries (`{ timeZone: "Europe/Amsterdam", … }`).
// ---------------------------------------------------------------------------

const intlOptions = (): Type => opt(tCon(T_OBJECT, [tLabelVar('k'), tAnyType]));
const intlLocales = (): Type => opt(tUnion([tString, tArray(tString)]));

const dateTimeFormatPart = (): Type => tRecord({ type: tString, value: tString });

const dateTimeFormatMethods: Record<string, MethodEntry> = {
  format:          fn(opt(tCon('Date')), tString, '(Date | Undefined) -> String'),
  formatToParts:   fn(opt(tCon('Date')), tArray(dateTimeFormatPart()), '(Date | Undefined) -> [{ type :: String, value :: String }]'),
  resolvedOptions: fn(tVoid, tCon(T_OBJECT, [tLabelVar('k'), tAnyType]), '() -> Object k Any'),
};

const numberFormatMethods: Record<string, MethodEntry> = {
  format: fn(tNumber, tString, 'Number -> String'),
};

const intlMethods: Record<string, MethodEntry> = {
  DateTimeFormat: {
    signature: '(String | [String] | Undefined, Object k Any | Undefined) -> DateTimeFormat',
    factory: () => tFun(tTuple([intlLocales(), intlOptions()]), tCon('DateTimeFormat')),
    isStatic: true,
  },
  NumberFormat: {
    signature: '(String | [String] | Undefined, Object k Any | Undefined) -> NumberFormat',
    factory: () => tFun(tTuple([intlLocales(), intlOptions()]), tCon('NumberFormat')),
    isStatic: true,
  },
};

const processMethods: Record<string, MethodEntry> = {
  // Properties
  argv:     prop(tArray(tString),  '[String]'),
  argv0:    prop(tString,          'String'),
  execArgv: prop(tArray(tString),  '[String]'),
  execPath: prop(tString,          'String'),
  pid:      prop(tNumber,          'Number'),
  ppid:     prop(tNumber,          'Number'),
  platform: prop(tString,          'String'),
  arch:     prop(tString,          'String'),
  version:  prop(tString,          'String'),
  versions: prop(processVersionsRecord,
    '{ node :: String, v8 :: String, modules :: String, uv :: String, zlib :: String, ares :: String, openssl :: String }'),
  // `process.env` is an open index-signature object whose values are all
  // strings (Node coerces every environment variable to a String), so e.g.
  // `process.env.NODE_ENV :: String` for any key without an explicit
  // declaration.  A fresh label var per access keeps the row open; it carries
  // the display name `k` so hover shows `Object k String` rather than the raw
  // id-derived `k<n>`.
  env:      { signature: 'Object k String', factory: () => tCon(T_OBJECT, [tLabelVar('k'), tString]) },
  title:    prop(tString,          'String'),
  exitCode: prop(tNumber,          'Number'),
  stdin:    prop(tAnyType,         'Any'),
  stdout:   { signature: PROCESS_STREAM_SIG, factory: processStreamRecord },
  stderr:   { signature: PROCESS_STREAM_SIG, factory: processStreamRecord },
  // Methods
  exit:        fn(tNumber, tVoid, 'Number -> ()'),
  cwd:         fn(tVoid, tString, '() -> String'),
  chdir:       fn(tString, tVoid, 'String -> ()'),
  nextTick:    fn(tFun(tVoid, tVoid), tVoid, '(() -> ()) -> ()'),
  hrtime:      fn(tVoid, tTuple([tNumber, tNumber]), '() -> (Number, Number)'),
  uptime:      fn(tVoid, tNumber, '() -> Number'),
  memoryUsage: fn(tVoid, processMemoryUsageRecord,
    '() -> { rss :: Number, heapTotal :: Number, heapUsed :: Number, external :: Number, arrayBuffers :: Number }'),
  kill:        fn(tTuple([tNumber, tString]), tBool, '(Number, String) -> Boolean'),
  emit: {
    signature: '(String, a) -> Boolean',
    factory: () => tFun(tTuple([tString, tVar('a')]), tBool),
  },
  ...bulk(
    ['on', 'once', 'off', 'addListener', 'removeListener'],
    {
      signature: '(String, a -> ()) -> Process',
      factory: () => tFun(tTuple([tString, tFun(tVar('a'), tVoid)]), tCon('Process')),
    },
  ),
};

// ---------------------------------------------------------------------------
// Node.js `Buffer` — statics on the `Buffer` global TCon, instance methods
// on TCon('Buffer') values.  Statics share the same map and are flagged
// with `isStatic: true`.
// ---------------------------------------------------------------------------

const bufferMethods: Record<string, MethodEntry> = {
  // Statics
  from: {
    signature: 'a -> Buffer',
    factory: () => tFun(tVar('a'), tCon('Buffer')),
    isStatic: true,
  },
  alloc: {
    signature: 'Number -> Buffer',
    factory: () => tFun(tNumber, tCon('Buffer')),
    isStatic: true,
  },
  allocUnsafe: {
    signature: 'Number -> Buffer',
    factory: () => tFun(tNumber, tCon('Buffer')),
    isStatic: true,
  },
  isBuffer: {
    signature: 'a -> Boolean',
    factory: () => tFun(tVar('a'), tBool),
    isStatic: true,
  },
  concat: {
    signature: '[Buffer] -> Buffer',
    factory: () => tFun(tArray(tCon('Buffer')), tCon('Buffer')),
    isStatic: true,
  },
  byteLength: {
    signature: 'String -> Number',
    factory: () => tFun(tString, tNumber),
    isStatic: true,
  },
  // Instance
  length:   prop(tNumber, 'Number'),
  // `buf.toString ()` / `buf.toString ("utf8")` (Node: an optional encoding).
  toString: { signature: '(String | Undefined) -> String', factory: () => tFun(opt(tString), tString) },
  slice:    fn(tTuple([tNumber, tNumber]), tCon('Buffer'), '(Number, Number) -> Buffer'),
  write:    fn(tString, tNumber, 'String -> Number'),
  equals:   fn(tCon('Buffer'), tBool, 'Buffer -> Boolean'),
  fill: {
    signature: 'a -> Buffer',
    factory: () => tFun(tVar('a'), tCon('Buffer')),
  },
  readUInt8:  fn(tNumber, tNumber, 'Number -> Number'),
  readUInt16BE: fn(tNumber, tNumber, 'Number -> Number'),
  readUInt16LE: fn(tNumber, tNumber, 'Number -> Number'),
  readUInt32BE: fn(tNumber, tNumber, 'Number -> Number'),
  readUInt32LE: fn(tNumber, tNumber, 'Number -> Number'),
  writeUInt8: {
    signature: '(Number, Number) -> Number',
    factory: () => tFun(tTuple([tNumber, tNumber]), tNumber),
  },
};

// ---------------------------------------------------------------------------
// Typed arrays (Uint8Array, Int8Array, Float64Array, …) + ArrayBuffer/DataView
// ---------------------------------------------------------------------------

/**
 * Build the method bag shared by the typed-array family.  `self` is the
 * concrete view type name (e.g. `'Uint8Array'`) and `elem` is its element
 * primitive (`Number` for the integer/float views, `BigInt` for the
 * `BigInt64`/`BigUint64` views).  Typed arrays are arity-0 builtins: the
 * element type is fixed by the view, not a generic parameter.
 */
function typedArrayMethods(self: string, elem: Type, elemName: string): Record<string, MethodEntry> {
  const selfT = tCon(self, []);
  return {
    // Properties
    length: prop(tNumber, 'Number'),
    byteLength: prop(tNumber, 'Number'),
    byteOffset: prop(tNumber, 'Number'),
    BYTES_PER_ELEMENT: prop(tNumber, 'Number'),
    // Statics
    of: {
      signature: `a -> ${self}`,
      factory: () => tFun(tVar('a'), selfT),
      isStatic: true,
    },
    from: {
      signature: `a -> ${self}`,
      factory: () => tFun(tVar('a'), selfT),
      isStatic: true,
    },
    // Instance methods
    at: fn(tNumber, opt(elem), `Number -> (${elemName} | Undefined)`),
    set: { signature: 'a -> Undefined', factory: () => tFun(tVar('a'), tUndefined) },
    fill: fn(elem, selfT, `${elemName} -> ${self}`),
    slice: {
      signature: `(Number | Undefined, Number | Undefined) -> ${self}`,
      factory: () => tFun(tTuple([opt(tNumber), opt(tNumber)]), selfT),
    },
    subarray: {
      signature: `(Number | Undefined, Number | Undefined) -> ${self}`,
      factory: () => tFun(tTuple([opt(tNumber), opt(tNumber)]), selfT),
    },
    indexOf: fn(elem, tNumber, `${elemName} -> Number`),
    includes: fn(elem, tBool, `${elemName} -> Boolean`),
    join: { signature: '(String | Undefined) -> String', factory: () => tFun(opt(tString), tString) },
    reverse: fn(tVoid, selfT, `() -> ${self}`),
    map: { signature: `(${elemName} -> ${elemName}) -> ${self}`, factory: () => tFun(tFun(elem, elem), selfT) },
    forEach: { signature: `(${elemName} -> b) -> Undefined`, factory: () => tFun(tFun(elem, tVar('b')), tUndefined) },
    filter: { signature: `(${elemName} -> Boolean) -> ${self}`, factory: () => tFun(tFun(elem, tBool), selfT) },
    toString: toStringMethod(),
  };
}

/** The arity-0 typed-array view type names and their element primitive. */
const TYPED_ARRAY_TYPES: ReadonlyArray<readonly [string, Type, string]> = [
  ['Int8Array', tNumber, 'Number'],
  ['Uint8Array', tNumber, 'Number'],
  ['Uint8ClampedArray', tNumber, 'Number'],
  ['Int16Array', tNumber, 'Number'],
  ['Uint16Array', tNumber, 'Number'],
  ['Int32Array', tNumber, 'Number'],
  ['Uint32Array', tNumber, 'Number'],
  ['Float32Array', tNumber, 'Number'],
  ['Float64Array', tNumber, 'Number'],
  ['BigInt64Array', tCon('BigInt'), 'BigInt'],
  ['BigUint64Array', tCon('BigInt'), 'BigInt'],
];

const arrayBufferMethods: Record<string, MethodEntry> = {
  byteLength: prop(tNumber, 'Number'),
  slice: {
    signature: '(Number | Undefined, Number | Undefined) -> ArrayBuffer',
    factory: () => tFun(tTuple([opt(tNumber), opt(tNumber)]), tCon('ArrayBuffer')),
  },
  isView: {
    signature: 'a -> Boolean',
    factory: () => tFun(tVar('a'), tBool),
    isStatic: true,
  },
};

const dataViewMethods: Record<string, MethodEntry> = {
  byteLength: prop(tNumber, 'Number'),
  byteOffset: prop(tNumber, 'Number'),
  buffer: prop(tCon('ArrayBuffer'), 'ArrayBuffer'),
  ...bulk(
    ['getInt8', 'getUint8', 'getInt16', 'getUint16',
     'getInt32', 'getUint32', 'getFloat32', 'getFloat64'],
    fn(tNumber, tNumber, 'Number -> Number'),
  ),
  ...bulk(
    ['setInt8', 'setUint8', 'setInt16', 'setUint16',
     'setInt32', 'setUint32', 'setFloat32', 'setFloat64'],
    { signature: '(Number, Number) -> Undefined', factory: () => tFun(tTuple([tNumber, tNumber]), tUndefined) },
  ),
};

// ---------------------------------------------------------------------------
// Generator methods (Generator y).  `y` is the yielded element type, taken
// from the receiver's single type argument.  `next`/`return`/`throw` each
// produce an iterator-result record `{ done: Boolean, value: y }`.
// ---------------------------------------------------------------------------

function iterResult(typeArgs: Type[]): Type {
  return tRecord({ done: tBool, value: elemVar(typeArgs) });
}

const generatorMethods: Record<string, MethodEntry> = {
  next: {
    signature: '() -> { done :: Boolean, value :: a }',
    factory: (typeArgs) => tFun(tVoid, iterResult(typeArgs)),
  },
  return: {
    signature: 'a -> { done :: Boolean, value :: a }',
    factory: (typeArgs) => tFun(elemVar(typeArgs), iterResult(typeArgs)),
  },
  throw: {
    signature: 'a -> { done :: Boolean, value :: b }',
    factory: (typeArgs) => tFun(tVar('a'), iterResult(typeArgs)),
  },
};

// ---------------------------------------------------------------------------
// Reflect methods (all static)
// ---------------------------------------------------------------------------

const reflectMethods: Record<string, MethodEntry> = {
  get: {
    signature: '(a, String) -> b',
    factory: () => tFun(tTuple([tVar('a'), tString]), tVar('b')),
    isStatic: true,
  },
  set: {
    signature: '(a, String, b) -> Boolean',
    factory: () => tFun(tTuple([tVar('a'), tString, tVar('b')]), tBool),
    isStatic: true,
  },
  has: {
    signature: '(a, String) -> Boolean',
    factory: () => tFun(tTuple([tVar('a'), tString]), tBool),
    isStatic: true,
  },
  deleteProperty: {
    signature: '(a, String) -> Boolean',
    factory: () => tFun(tTuple([tVar('a'), tString]), tBool),
    isStatic: true,
  },
  ownKeys: {
    signature: 'a -> [String]',
    factory: () => tFun(tVar('a'), tArray(tString)),
    isStatic: true,
  },
  getPrototypeOf: {
    signature: 'a -> b',
    factory: () => tFun(tVar('a'), tVar('b')),
    isStatic: true,
  },
  setPrototypeOf: {
    signature: '(a, b) -> Boolean',
    factory: () => tFun(tTuple([tVar('a'), tVar('b')]), tBool),
    isStatic: true,
  },
  isExtensible: {
    signature: 'a -> Boolean',
    factory: () => tFun(tVar('a'), tBool),
    isStatic: true,
  },
  preventExtensions: {
    signature: 'a -> Boolean',
    factory: () => tFun(tVar('a'), tBool),
    isStatic: true,
  },
  defineProperty: {
    signature: '(a, String, b) -> Boolean',
    factory: () => tFun(tTuple([tVar('a'), tString, tVar('b')]), tBool),
    isStatic: true,
  },
  getOwnPropertyDescriptor: {
    signature: '(a, String) -> b',
    factory: () => tFun(tTuple([tVar('a'), tString]), tVar('b')),
    isStatic: true,
  },
  apply: {
    signature: '(Function, a, [b]) -> c',
    factory: () => tFun(tTuple([tCon('Function', []), tVar('a'), tArray(tVar('b'))]), tVar('c')),
    isStatic: true,
  },
  construct: {
    signature: '(Function, [a]) -> b',
    factory: () => tFun(tTuple([tCon('Function', []), tArray(tVar('a'))]), tVar('b')),
    isStatic: true,
  },
};

// ---------------------------------------------------------------------------
// Registry class
// ---------------------------------------------------------------------------

/** Encapsulates method registry state and operations. */
export class MethodRegistry {
  /** Container type name -> method name -> MethodEntry */
  private methods: Record<string, Record<string, MethodEntry>>;
  /** Parallel namespace for static methods that collide with an existing
   *  instance method of the same name (e.g. user declares
   *  `// Array.every :: ...` while the built-in instance `Array#every`
   *  also exists).  Without this split, registering the static would
   *  overwrite the instance entry and corrupt downstream `[].every`
   *  inference.  Statics that do NOT collide with an instance still go
   *  into `methods` (e.g. `Array.from`, `Array.of`) — keeping legacy
   *  lookup paths intact. */
  private staticMethods: Record<string, Record<string, MethodEntry>>;
  /** Number of type parameters per registered type */
  private arities: Record<string, number>;
  /** Type names whose `methods`/`arities` slots were mutated since the last
   *  `clearCustom()` (via register/restore/merge/restoreBuiltinOriginalEntries).
   *  `clearCustom()` only needs to visit these instead of scanning every
   *  built-in type's full method bag on each inference pass. */
  private dirtyTypes = new Set<string>();
  /** Standalone `// ::hidden` markers: typeName -> set of method names that
   *  should be hidden from completion even when registered without an
   *  explicit `hidden` flag (e.g. above a class method without annotation). */
  private hiddenStandalone: Record<string, Set<string>>;
  /** Standalone `// ::private` markers: typeName -> set of method names that
   *  are private to the owning type.  Implies hidden. */
  private privateStandalone: Record<string, Set<string>>;
  /** AST node start offsets of properties marked hidden by a standalone
   *  `// ::hidden` directive (used to filter object-literal record fields). */
  private hiddenPropertyOffsets: Set<number>;
  /** Original method keys for built-in types (used to remove custom additions). */
  private readonly builtinMethodKeys: Record<string, Set<string>>;
  /** Original method entries on built-in types as they existed at
   *  construction time.  Used by `clearCustom()` to revert any runtime
   *  override on a built-in original key (e.g. an imported file declaring
   *  `// Array#every :: ...`) and by `snapshot()` to detect overrides. */
  private readonly originalBuiltinEntries: Record<string, Record<string, MethodEntry>>;

  /** Built-in type names whose registrations are never cleared. */
  private static readonly BUILTIN_TYPES = new Set([
    'Array', 'String', 'Console', 'Math', 'Promise',
    'Map', 'Set', 'RegExp', 'Number', 'Boolean',
    'Error', 'TypeError', 'RangeError', 'ReferenceError', 'SyntaxError',
    'Function', 'Object', 'Date', 'Symbol', 'BigInt', 'JSON', 'Reflect',
    'Process', 'Buffer', 'Performance', 'Intl', 'DateTimeFormat', 'NumberFormat',
    // Typed arrays + binary buffers (all arity-0 views).
    'Int8Array', 'Uint8Array', 'Uint8ClampedArray', 'Int16Array', 'Uint16Array',
    'Int32Array', 'Uint32Array', 'Float32Array', 'Float64Array',
    'BigInt64Array', 'BigUint64Array', 'ArrayBuffer', 'DataView',
    // Generator (arity-1): the result of calling a `function*`.
    'Generator',
    // DOM & Fetch nominal types (see domGlobals.ts).  Always in the builtin
    // set so `::global Element#member :: …` extensions survive clearCustom;
    // whether the typed GLOBALS (`document`, …) use them is gated behind the
    // `dom.globalTypes` setting (Response/fetch is always on).
    'Document', 'Element', 'Window', 'Storage', 'Event', 'Navigator', 'Response',
    'AbortSignal', 'AbortSignalStatics', 'AbortController', 'URLSearchParams', 'URL',
    // `Null` / `Undefined` are first-class TCons (`tNull`, `tUndefined`) and
    // valid receivers for user-declared method annotations such as
    // `// Null#equals :: Null ~> Null -> Boolean`.  They have no preloaded
    // method bag — the constructor below seeds an empty one so user
    // registrations from `processMethodAnnotations` land in a real bag and
    // survive `clearCustomMethods` cycles like any other builtin.
    'Null', 'Undefined',
  ]);

  static isBuiltin(typeName: string): boolean {
    return MethodRegistry.BUILTIN_TYPES.has(typeName);
  }

  constructor() {
    this.methods = {
      Array: arrayMethods,
      String: stringMethods,
      Promise: promiseMethods,
      Map: mapMethods,
      Set: setMethods,
      RegExp: regexpMethods,
      Number: numberMethods,
      Boolean: booleanMethods,
      Error: errorMethods,
      TypeError: errorMethods,
      RangeError: errorMethods,
      ReferenceError: errorMethods,
      SyntaxError: errorMethods,
      Function: functionMethods,
      Math: mathMethods,
      Object: objectMethods,
      Date: dateMethods,
      Symbol: symbolMethods,
      BigInt: bigintMethods,
      JSON: jsonMethods,
      Console: consoleMethods,
      Reflect: reflectMethods,
      Process: processMethods,
      Performance: performanceMethods,
      Intl: intlMethods,
      DateTimeFormat: dateTimeFormatMethods,
      NumberFormat: numberFormatMethods,
      Buffer: bufferMethods,
      ArrayBuffer: arrayBufferMethods,
      DataView: dataViewMethods,
      Generator: generatorMethods,
      // DOM & Fetch method bags (compact catalogue; strict-null mode
      // defaults off — `applyDomSettings` rebuilds these on change).
      ...buildDomMethodTables(isDomStrictNulls()),
    };
    this.arities = {
      Array: 1,
      String: 0,
      Promise: 2,
      Map: 2,
      Set: 1,
      RegExp: 0,
      Number: 0,
      Boolean: 0,
      Error: 0,
      TypeError: 0,
      RangeError: 0,
      ReferenceError: 0,
      SyntaxError: 0,
      Function: 0,
      Math: 0,
      Object: 0,
      Date: 0,
      Symbol: 0,
      BigInt: 0,
      JSON: 0,
      Console: 0,
      Reflect: 0,
      Process: 0,
      Performance: 0,
      Intl: 0,
      DateTimeFormat: 0,
      NumberFormat: 0,
      Buffer: 0,
    };
    // Typed-array views: seed each shared method bag and arity 0.
    for (const [name, elem, elemName] of TYPED_ARRAY_TYPES) {
      this.methods[name] = typedArrayMethods(name, elem, elemName);
      this.arities[name] = 0;
    }
    this.arities.ArrayBuffer = 0;
    this.arities.DataView = 0;
    this.arities.Generator = 1;
    // Seed any BUILTIN_TYPES entry that lacks a preloaded method bag so
    // that `clearCustom()` can wipe user-added methods on it without
    // leaking (the guard there requires `builtinMethodKeys[name]` to be
    // defined — see snapshot loop below).  Covers Console as well as the
    // native global types Object/Date/Symbol/BigInt.
    for (const typeName of MethodRegistry.BUILTIN_TYPES) {
      if (!this.methods[typeName]) this.methods[typeName] = {};
      if (this.arities[typeName] === undefined) this.arities[typeName] = 0;
    }
    // Snapshot the original built-in method keys so clearCustom() can
    // remove methods that were added to built-in types by ::global/::types.
    this.builtinMethodKeys = {};
    this.originalBuiltinEntries = {};
    for (const typeName of MethodRegistry.BUILTIN_TYPES) {
      if (this.methods[typeName]) {
        this.builtinMethodKeys[typeName] = new Set(Object.keys(this.methods[typeName]));
        // Also retain the original entries themselves so we can revert
        // user-issued overrides on built-in original keys (e.g. an
        // imported file declaring `// Array#every :: ...` mutates the
        // global `Array.every` slot — we need the pre-mutation value to
        // restore on `clearCustom()`).
        this.originalBuiltinEntries[typeName] = { ...this.methods[typeName] };
      }
    }
    this.hiddenStandalone = {};
    this.privateStandalone = {};
    this.hiddenPropertyOffsets = new Set();
    this.staticMethods = {};
  }

  /** Mark `(typeName, methodName)` as hidden from completion. Used by
   *  standalone `// ::hidden` directives. The flag persists across
   *  registrations and is consulted by `isHidden`. */
  markHidden(typeName: string, methodName: string): void {
    if (!this.hiddenStandalone[typeName]) this.hiddenStandalone[typeName] = new Set();
    this.hiddenStandalone[typeName].add(methodName);
  }

  /** Mark an AST property node start offset as hidden. Used to filter the
   *  property out of the inferred record type. */
  markHiddenPropertyOffset(start: number): void {
    this.hiddenPropertyOffsets.add(start);
  }

  /** Returns true if the AST property node at `start` was marked hidden. */
  isHiddenPropertyOffset(start: number): boolean {
    return this.hiddenPropertyOffsets.has(start);
  }

  /** Returns true if (typeName, methodName) was marked hidden via `::hidden`
   *  standalone, or its registered entry has `hidden: true`. */
  isHidden(typeName: string, methodName: string): boolean {
    if (this.hiddenStandalone[typeName]?.has(methodName)) return true;
    if (this.privateStandalone[typeName]?.has(methodName)) return true;
    const entry = this.methods[typeName]?.[methodName];
    return !!entry?.hidden || !!entry?.private;
  }

  /** Mark `(typeName, methodName)` as private.  Used by standalone
   *  `// ::private` directives.  Private members are also hidden from
   *  completion (privacy implies hidden). */
  markPrivate(typeName: string, methodName: string): void {
    if (!this.privateStandalone[typeName]) this.privateStandalone[typeName] = new Set();
    this.privateStandalone[typeName].add(methodName);
  }

  /** Returns true if (typeName, methodName) was marked private via `::private`
   *  standalone, or its registered entry has `private: true`. */
  isPrivate(typeName: string, methodName: string): boolean {
    if (this.privateStandalone[typeName]?.has(methodName)) return true;
    return !!this.methods[typeName]?.[methodName]?.private;
  }

  /** Look up a method on a container type. Returns null if not registered.
   *  Consults the parallel `staticMethods` namespace only if no entry is
   *  found in `methods` — preserves legacy precedence (instance preferred
   *  on collision, since most call sites are member-access on values). */
  /** `[a, b, ...]` annotations carry the internal `SpreadArray` constructor,
   *  which is a positional view of a plain JS array.  For method and
   *  typeclass-constraint resolution it behaves exactly like `Array`, so
   *  normalize it here (element/positional typing stays in inferArrayExpression). */
  private static normalizeReceiver(typeName: string): string {
    return typeName === T_SPREAD_ARRAY ? 'Array' : typeName;
  }

  lookup(typeName: string, methodName: string): MethodEntry | null {
    typeName = MethodRegistry.normalizeReceiver(typeName);
    const methods = this.methods[typeName];
    if (methods && Object.prototype.hasOwnProperty.call(methods, methodName)) {
      return methods[methodName] ?? null;
    }
    const statics = this.staticMethods[typeName];
    if (statics && Object.prototype.hasOwnProperty.call(statics, methodName)) {
      return statics[methodName] ?? null;
    }
    return null;
  }

  /** Look up a static method specifically (skips the instance namespace). */
  lookupStatic(typeName: string, methodName: string): MethodEntry | null {
    typeName = MethodRegistry.normalizeReceiver(typeName);
    const primary = this.methods[typeName]?.[methodName];
    if (primary && primary.isStatic) return primary;
    const overflow = this.staticMethods[typeName]?.[methodName];
    return overflow ?? null;
  }

  /** Get all registered method names for a type (union of instance and
   *  static namespaces — callers that care filter by `entry.isStatic`). */
  getMethodNames(typeName: string): string[] {
    typeName = MethodRegistry.normalizeReceiver(typeName);
    // `@@new` is the internal constructor signature (`T.@@new`, registered
    // from a constructor annotation so a `TypeRep T` is callable); it is not
    // a member, and counting it would make a type look "registered" and
    // disable the lenient lookup of members of otherwise unregistered types.
    const fromMethods = Object.keys(this.methods[typeName] ?? {}).filter((k) => k !== '@@new');
    const fromStatics = Object.keys(this.staticMethods[typeName] ?? {}).filter((k) => k !== '@@new');
    if (fromStatics.length === 0) return fromMethods;
    const seen = new Set(fromMethods);
    for (const k of fromStatics) seen.add(k);
    return Array.from(seen);
  }

  /** Register a custom method on a type.  Statics whose name collides with
   *  an existing non-static entry land in the parallel `staticMethods`
   *  namespace so both can coexist. */
  register(typeName: string, methodName: string, entry: MethodEntry, arity?: number): void {
    this.dirtyTypes.add(typeName);
    if (!this.methods[typeName]) {
      this.methods[typeName] = {};
    }
    const existing = this.methods[typeName][methodName];
    if (entry.isStatic && existing && !existing.isStatic) {
      // Collision with an instance entry — keep both, route static aside.
      if (!this.staticMethods[typeName]) this.staticMethods[typeName] = {};
      this.staticMethods[typeName][methodName] = entry;
    } else {
      this.methods[typeName][methodName] = entry;
      // If we previously stored a colliding static here, keep it in sync
      // when an instance is being (re-)registered: leave the parallel
      // static slot untouched so it survives.
    }
    if (arity !== undefined) {
      this.arities[typeName] = arity;
    }
  }

  /** Get the type parameter arity of a registered type (0 if unknown). */
  getTypeArity(typeName: string): number {
    return this.arities[typeName] ?? 0;
  }

  /**
   * Swap in freshly built method bags for a set of built-in types (used
   * when the `dom.strictNulls` setting changes: signature strings must
   * match the mode).  User-added custom methods on those types (via
   * `::global`) are preserved; the original-keys/entries snapshots are
   * refreshed so `clearCustom()` reverts to the NEW factory entries.
   */
  replaceBuiltinTables(tables: Record<string, Record<string, MethodEntry>>): void {
    for (const [typeName, bag] of Object.entries(tables)) {
      const oldOriginalKeys = this.builtinMethodKeys[typeName] ?? new Set<string>();
      const existing = this.methods[typeName] ?? {};
      const custom: Record<string, MethodEntry> = {};
      for (const [methodName, entry] of Object.entries(existing)) {
        if (!oldOriginalKeys.has(methodName)) custom[methodName] = entry;
      }
      this.methods[typeName] = { ...bag, ...custom };
      this.builtinMethodKeys[typeName] = new Set(Object.keys(bag));
      this.originalBuiltinEntries[typeName] = { ...bag };
    }
  }

  /** Clear all custom (non-built-in) method registrations. */
  clearCustom(): void {
    for (const typeName of this.dirtyTypes) {
      if (!MethodRegistry.BUILTIN_TYPES.has(typeName)) {
        delete this.methods[typeName];
        delete this.arities[typeName];
      } else {
        // Built-in type: delete custom non-original keys, and revert
        // any user-issued OVERRIDE on an original key back to the
        // factory-time entry (so a stale `Array#every` override does
        // not bleed into the next inference pass).
        const originalKeys = this.builtinMethodKeys[typeName];
        const originals = this.originalBuiltinEntries[typeName];
        if (originalKeys && this.methods[typeName]) {
          for (const methodName of Object.keys(this.methods[typeName])) {
            if (!originalKeys.has(methodName)) {
              delete this.methods[typeName][methodName];
            } else if (originals && this.methods[typeName][methodName] !== originals[methodName]) {
              this.methods[typeName][methodName] = originals[methodName];
            }
          }
        }
      }
    }
    this.dirtyTypes.clear();
    // Standalone hidden markers are per-source — drop them on every clear.
    this.hiddenStandalone = {};
    this.privateStandalone = {};
    this.hiddenPropertyOffsets = new Set();
    // Parallel-namespace statics are always user-registered (collision
    // overflow), never preloaded — wipe them entirely.
    this.staticMethods = {};
  }

  /** Get all currently registered type names. */
  getRegisteredTypeNames(): Set<string> {
    return new Set(Object.keys(this.methods));
  }

  /** Singleton/namespace types whose methods exist only on the global
   *  instance (e.g. `console`, `Math`).  Their methods must never coerce
   *  a TVar receiver via {@link findMethodCandidates} — a user class
   *  writing `this.log = 0` should not bind `this` to `Console`. */
  private static readonly SINGLETON_NAMESPACES = new Set([
    'Math', 'Console', 'JSON', 'Reflect', 'Object', 'Performance', 'Intl',
    // Fetch helpers: a TVar receiver using `.aborted` or `.get` is not an
    // AbortSignal or URLSearchParams (`m => m.get (k)` stays a Map).
    'AbortSignal', 'AbortSignalStatics', 'AbortController', 'URLSearchParams', 'URL',
  ]);

  /** Find all registered types that have a given method/property. */
  findMethodCandidates(methodName: string): [string, MethodEntry][] {
    const candidates: [string, MethodEntry][] = [];
    for (const [typeName, methods] of Object.entries(this.methods)) {
      if (MethodRegistry.SINGLETON_NAMESPACES.has(typeName)) continue;
      if (Object.prototype.hasOwnProperty.call(methods, methodName) && methods[methodName]) {
        candidates.push([typeName, methods[methodName]]);
      }
    }
    return candidates;
  }

  /**
   *  Snapshot the CURRENT entries that occupy original built-in method
   *  keys (e.g. `Array.every`, `String.split`).  Used by scan-triggered
   *  inference paths (like `getWorkspaceExports`) so they can roll back
   *  any side-effect overwrites a scanned file may perform via
   *  `register()` (a shorthand annotation `// Array.every :: ...` in a
   *  workspace-sibling file must not corrupt the global registry).
   *  Custom additions on non-original keys are NOT captured — they survive
   *  the restore, which is the desired behaviour (completion needs them).
   */
  snapshotBuiltinOriginalEntries(): Record<string, Record<string, MethodEntry>> {
    const out: Record<string, Record<string, MethodEntry>> = {};
    for (const typeName of MethodRegistry.BUILTIN_TYPES) {
      const originalKeys = this.builtinMethodKeys[typeName];
      const entries = this.methods[typeName];
      if (!originalKeys || !entries) continue;
      const captured: Record<string, MethodEntry> = {};
      let any = false;
      for (const key of originalKeys) {
        if (entries[key] !== undefined) {
          captured[key] = entries[key];
          any = true;
        }
      }
      if (any) out[typeName] = captured;
    }
    return out;
  }

  /** Restore previously-snapshotted original built-in method entries. */
  restoreBuiltinOriginalEntries(snap: Record<string, Record<string, MethodEntry>>): void {
    for (const [typeName, entries] of Object.entries(snap)) {
      this.dirtyTypes.add(typeName);
      if (!this.methods[typeName]) this.methods[typeName] = {};
      for (const [methodName, entry] of Object.entries(entries)) {
        this.methods[typeName][methodName] = entry;
      }
    }
  }

  /** Save a snapshot of all custom (non-built-in) registrations. */
  snapshot(): MethodRegistrySnapshot {
    const methods: Record<string, Record<string, MethodEntry>> = {};
    const arities: Record<string, number> = {};
    for (const [typeName, entries] of Object.entries(this.methods)) {
      if (!MethodRegistry.BUILTIN_TYPES.has(typeName)) {
        methods[typeName] = { ...entries };
      } else {
        // For built-in types, snapshot:
        //  - custom non-original methods, AND
        //  - user-issued OVERRIDES on original keys (entry differs from
        //    the factory-time built-in entry).  Without the override
        //    branch, an `// Array#every :: ...` redefinition declared in
        //    an imported file would never be carried back to the host's
        //    inference pass.
        const originalKeys = this.builtinMethodKeys[typeName];
        const originals = this.originalBuiltinEntries[typeName];
        if (originalKeys) {
          const customEntries: Record<string, MethodEntry> = {};
          let hasCustom = false;
          for (const [mn, entry] of Object.entries(entries)) {
            if (!originalKeys.has(mn)) {
              customEntries[mn] = entry;
              hasCustom = true;
            } else if (originals && entry !== originals[mn]) {
              customEntries[mn] = entry;
              hasCustom = true;
            }
          }
          if (hasCustom) {
            methods[typeName] = customEntries;
          }
        }
      }
    }
    for (const [typeName, a] of Object.entries(this.arities)) {
      if (!MethodRegistry.BUILTIN_TYPES.has(typeName)) {
        arities[typeName] = a;
      }
    }
    // Parallel-namespace statics are always custom — snapshot verbatim.
    let staticMethods: Record<string, Record<string, MethodEntry>> | undefined;
    for (const [typeName, entries] of Object.entries(this.staticMethods)) {
      if (Object.keys(entries).length === 0) continue;
      if (!staticMethods) staticMethods = {};
      staticMethods[typeName] = { ...entries };
    }
    return staticMethods ? { methods, arities, staticMethods } : { methods, arities };
  }

  /** Restore custom registrations from a snapshot. */
  restore(snap: MethodRegistrySnapshot): void {
    this.clearCustom();
    for (const [typeName, entries] of Object.entries(snap.methods)) {
      this.dirtyTypes.add(typeName);
      if (MethodRegistry.BUILTIN_TYPES.has(typeName)) {
        // For built-in types, merge custom methods back onto the existing type
        for (const [methodName, entry] of Object.entries(entries)) {
          this.methods[typeName][methodName] = entry;
        }
      } else {
        this.methods[typeName] = { ...entries };
      }
    }
    for (const [typeName, a] of Object.entries(snap.arities)) {
      this.dirtyTypes.add(typeName);
      this.arities[typeName] = a;
    }
    // Re-seed parallel-namespace statics from the snapshot (clearCustom
    // wiped them above).
    if (snap.staticMethods) {
      for (const [typeName, entries] of Object.entries(snap.staticMethods)) {
        this.staticMethods[typeName] = { ...entries };
      }
    }
  }

  /** Merge a snapshot's registrations (non-destructive). */
  merge(snap: MethodRegistrySnapshot): void {
    for (const [typeName, entries] of Object.entries(snap.methods)) {
      this.dirtyTypes.add(typeName);
      if (!this.methods[typeName]) {
        this.methods[typeName] = {};
      }
      const isBuiltin = MethodRegistry.BUILTIN_TYPES.has(typeName);
      const originalKeys = isBuiltin ? this.builtinMethodKeys[typeName] : undefined;
      const originals = isBuiltin ? this.originalBuiltinEntries[typeName] : undefined;
      for (const [methodName, entry] of Object.entries(entries)) {
        const cur = this.methods[typeName][methodName];
        if (!cur) {
          this.methods[typeName][methodName] = entry;
        } else if (
          isBuiltin && originalKeys?.has(methodName) && originals
          && cur === originals[methodName] && entry !== originals[methodName]
        ) {
          // Snap carries a user override on a built-in original key and
          // the live slot still holds the factory-time entry: apply the
          // override so explicit imports of the file persist their
          // re-definition into the host's inference pass.
          this.methods[typeName][methodName] = entry;
        }
      }
    }
    for (const [typeName, a] of Object.entries(snap.arities)) {
      if (this.arities[typeName] === undefined) {
        this.dirtyTypes.add(typeName);
        this.arities[typeName] = a;
      }
    }
    // Parallel-namespace statics: merge non-destructively as well.  These
    // entries only exist when there was an instance/static name collision
    // in the source file, so they always carry intentional user data.
    if (snap.staticMethods) {
      for (const [typeName, entries] of Object.entries(snap.staticMethods)) {
        if (!this.staticMethods[typeName]) this.staticMethods[typeName] = {};
        for (const [methodName, entry] of Object.entries(entries)) {
          if (!this.staticMethods[typeName][methodName]) {
            this.staticMethods[typeName][methodName] = entry;
          }
        }
      }
    }
  }
}

/** Default global registry instance (backward compatibility). */
const defaultRegistry = new MethodRegistry();

// ---------------------------------------------------------------------------
// Backward-compatible free functions (delegate to defaultRegistry)
// ---------------------------------------------------------------------------

/**
 * Look up a method on a container type.
 * Returns null if the type or method is not registered.
 */
export function lookupMethod(
  typeName: string,
  methodName: string,
): MethodEntry | null {
  return defaultRegistry.lookup(typeName, methodName);
}

/**
 * Look up a static method specifically.  When an instance and a static
 * share the same name (e.g. user declares `// Array.every :: ...` while
 * the built-in instance `Array#every` exists), the static is stored in
 * a parallel namespace and is only reachable through this function.
 */
export function lookupStaticMethod(
  typeName: string,
  methodName: string,
): MethodEntry | null {
  return defaultRegistry.lookupStatic(typeName, methodName);
}

/**
 * Get all registered method names for a type.
 */
export function getMethodNames(typeName: string): string[] {
  return defaultRegistry.getMethodNames(typeName);
}

/**
 * Check whether a type name is a built-in type (String, Number, Array, etc.)
 * as opposed to a user-defined type (Box, Building, etc.).
 */
export function isBuiltinType(typeName: string): boolean {
  return MethodRegistry.isBuiltin(typeName);
}

/**
 * Register a custom method on a type (useful for extensions).
 */
export function registerMethod(
  typeName: string,
  methodName: string,
  entry: MethodEntry,
  arity?: number,
): void {
  defaultRegistry.register(typeName, methodName, entry, arity);
}

/**
 * Get the type parameter arity of a registered type.
 * Returns 0 if unknown.
 */
export function getTypeArity(typeName: string): number {
  return defaultRegistry.getTypeArity(typeName);
}

/**
 * Clear all custom (non-built-in) method registrations.
 * Called at the start of each inference run to prevent stale registrations
 * from persisting across runs (e.g. when a `// ::types` directive is removed).
 */
export function clearCustomMethods(): void {
  defaultRegistry.clearCustom();
}


/**
 * Apply the `hinmil.dom.*` settings: updates the domGlobals module state,
 * rebuilds the DOM/Fetch method bags (so hover signatures reflect the
 * strict-null mode) and invalidates the cached default environment (so
 * `document`/`window`/… flip between typed TCons and `Any`).
 * Called by the LSP server whenever settings (re)load, and by tests.
 */
export function applyDomSettings(next: Partial<DomSettings>): void {
  setDomSettingsState(next);
  defaultRegistry.replaceBuiltinTables(buildDomMethodTables(isDomStrictNulls()));
  resetDefaultEnvCache();
}

/**
 * True when unknown members on `typeName` should silently resolve to `Any`
 * instead of "Property does not exist" — the DOM/Fetch catalogue is compact
 * by design (see domGlobals.ts).
 */
export function hasAnyFallbackMethods(typeName: string): boolean {
  return domHasAnyFallback(typeName);
}

/**
 * Mark `(typeName, methodName)` as hidden from completion (standalone
 * `// ::hidden` directive). Called by inference engine after parsing
 * standalone hidden markers from the source.
 */
export function markMethodHidden(typeName: string, methodName: string): void {
  defaultRegistry.markHidden(typeName, methodName);
}

/**
 * Returns true when `(typeName, methodName)` was marked hidden either via
 * a standalone `::hidden` directive or via a member-annotation `hidden` flag.
 */
export function isMethodHidden(typeName: string, methodName: string): boolean {
  return defaultRegistry.isHidden(typeName, methodName);
}

/**
 * Mark `(typeName, methodName)` as private to the owning type.  Used by
 * standalone `// ::private` directives (and inferred from annotation
 * `private: true` flags).  Privates are hidden from completion and
 * surface a diagnostic on outside access.
 */
export function markMethodPrivate(typeName: string, methodName: string): void {
  defaultRegistry.markPrivate(typeName, methodName);
}

/** Returns true when `(typeName, methodName)` was marked private. */
export function isMethodPrivate(typeName: string, methodName: string): boolean {
  return defaultRegistry.isPrivate(typeName, methodName);
}

/** Mark an object-literal property AST node start offset as hidden. */
export function markHiddenPropertyOffset(start: number): void {
  defaultRegistry.markHiddenPropertyOffset(start);
}

/** Returns true if the object-literal property at `start` was marked hidden. */
export function isHiddenPropertyOffset(start: number): boolean {
  return defaultRegistry.isHiddenPropertyOffset(start);
}

/**
 * Get all currently registered type names (both built-in and custom).
 */
export function getRegisteredTypeNames(): Set<string> {
  return defaultRegistry.getRegisteredTypeNames();
}

/**
 * Find all registered types that have a given method/property.
 * Returns list of [typeName, MethodEntry] pairs.
 */
export function findMethodCandidates(
  methodName: string,
): [string, MethodEntry][] {
  return defaultRegistry.findMethodCandidates(methodName);
}

/**
 * Container-IDENTITY methods: `(builtinType, method)` pairs whose presence is a
 * strong enough signal to coerce an otherwise-unconstrained receiver into that
 * built-in container.  Unlike generic structural methods (`map`, `reduce`,
 * `filter`, …) — which many types legitimately share and therefore must NOT
 * coerce (see `builtinSoleOwnerNoCoerce`) — these are identity-bearing container
 * operations owned by essentially one container (`Map#get`, `Set#add`), so
 * `x.get(k)` / `x.add(v)` on an unknown `x` may back-constrain `x` to `Map`/`Set`.
 */
const CONTAINER_IDENTITY_METHODS = new Set<string>([
  'Map.get',
  'Set.add',
]);

/** True when `(typeName, methodName)` is a container-identity method that may
 *  back-constrain an unconstrained receiver into the built-in container. */
export function isContainerIdentityMethod(typeName: string, methodName: string): boolean {
  return CONTAINER_IDENTITY_METHODS.has(`${typeName}.${methodName}`);
}

/** Snapshot type for saving/restoring registry state. */
export type MethodRegistrySnapshot = {
  methods: Record<string, Record<string, MethodEntry>>;
  arities: Record<string, number>;
  /** Parallel-namespace static registrations (collision overflow).  Always
   *  carried verbatim across snapshot/restore/merge. */
  staticMethods?: Record<string, Record<string, MethodEntry>>;
};

/** Save a snapshot of all custom (non-built-in) method registrations. */
export function snapshotMethodRegistry(): MethodRegistrySnapshot {
  return defaultRegistry.snapshot();
}

/** Restore custom method registrations from a snapshot. */
export function restoreMethodRegistry(snap: MethodRegistrySnapshot): void {
  defaultRegistry.restore(snap);
}

/** Merge a snapshot's registrations into the current registry (non-destructive). */
export function mergeMethodRegistry(snap: MethodRegistrySnapshot): void {
  defaultRegistry.merge(snap);
}

/** Snapshot current entries at original built-in method keys. */
export function snapshotBuiltinOriginalEntries(): Record<string, Record<string, MethodEntry>> {
  return defaultRegistry.snapshotBuiltinOriginalEntries();
}

/** Restore previously-snapshotted original built-in method entries. */
export function restoreBuiltinOriginalEntries(
  snap: Record<string, Record<string, MethodEntry>>,
): void {
  defaultRegistry.restoreBuiltinOriginalEntries(snap);
}
