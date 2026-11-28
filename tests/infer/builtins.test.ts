// Built-in type/constructor behaviour — consolidated suite.
//
//   1. Array polymorphism — built-in `Array` (constructor / TypeRep witness)
//      is bound with a quantified scheme, so each reference instantiates
//      FRESH variables; `const t = of (Array)` generalizes to `a -> [a]` and
//      later monomorphic calls do not retro-pin it.
//   2. `.constructor` access — Phase B + C + D: built-in `.constructor`
//      access typing, Array call-site union widening, and `Function(...)`
//      smart-infer from string args.
//   3. Sole-owner no-coerce — Fase 1 (#4/#7): a single BUILT-IN container
//      owner for a method name is not sufficient evidence to coerce an
//      unconstrained type variable into that container.
//   4. Namespace/type methods — parametrized smoke-tests for builtin
//      namespace/type methods registered in the method registry.
//   5. Object/Date/Symbol/BigInt — native JS global types are recognised as
//      first-class method-registry receivers; `// Object#concat :: ...` must
//      not trigger the orphan-method diagnostic.

import { InferenceEngine } from '../../src/infer';
import {
  resetTypeVarCounter,
  typeToString,
  prettyTypeToString,
} from '../../src/hm/types';
import type { Type } from '../../src/hm/types';
import { scrubSkolems } from '../../src/hm/typeUtils';
import { clearDataTypes } from '../../src/registries/dataTypeRegistry';
import {
  clearCustomMethods,
  findMethodCandidates,
  getMethodNames,
  isBuiltinType,
} from '../../src/registries/methodRegistry';

// ---------------------------------------------------------------------------
// 1. Regression: built-in `Array` (constructor / TypeRep witness) is
//    POLYMORPHIC.
//
// `Array` used to be bound `mono(a -> [a])` with a single cached element
// variable shared across the whole program (like `String`/`Number` once were).
// That made `const t = of (Array)` impossible to generalize — its result var
// was env-free (owned by the shared `Array` binding) — so a later
// `of (Array) (1)` retro-pinned `t`'s hover to `Number -> [Number]` and even a
// String call would have shown `String`.  `Array` (and `BigInt`) are now bound
// with a quantified scheme, so each reference instantiates FRESH variables.
//
// Mirrors fpkit `src/fl/of.spec.js`.
// ---------------------------------------------------------------------------

describe('built-in Array TypeRep polymorphism', () => {
  beforeEach(() => resetTypeVarCounter());

  const APPLICATIVE = '// ::constraint Applicative f { f :: { of :: a -> f a } }\n';
  const OF = '// of :: Applicative f => TypeRep f -> a -> f a\nconst of = T => x => T.of (x);\n';

  function hoverTypeAt(result: ReturnType<InferenceEngine['infer']>, off: number) {
    let bestStart = -1;
    let type: Type | null = null;
    for (const [start, { type: t, end }] of result.nodeTypes) {
      if (start <= off && off < end && start > bestStart) {
        type = result.substitution.apply(t);
        bestStart = start;
      }
    }
    return { bestStart, type };
  }

  test('const t = of (Array) generalizes to `a -> [a]`', () => {
    const src = `${APPLICATIVE}${OF}\nconst t = of (Array);\n`;
    const r = new InferenceEngine().infer(src);
    const { bestStart, type } = hoverTypeAt(r, src.indexOf('t = of'));
    expect(type).not.toBeNull();
    expect(prettyTypeToString(type!)).toBe('a -> [a]');
    // Generalized: the binding records a polymorphic scheme with one quantified var.
    expect(r.declaredSchemes?.get(bestStart)?.vars.length).toBe(1);
    expect(r.diagnostics).toHaveLength(0);
  });

  test('a later of (Array) (Number) call does NOT retro-pin `t`', () => {
    const src = `${APPLICATIVE}${OF}\nconst t = of (Array);\nconst u = of (Array) (1);\n`;
    const r = new InferenceEngine().infer(src);
    const { type } = hoverTypeAt(r, src.indexOf('t = of'));
    expect(prettyTypeToString(type!)).toBe('a -> [a]');
  });

  test('a later of (Array) (String) call does NOT retro-pin `t`', () => {
    const src = `${APPLICATIVE}${OF}\nconst t = of (Array);\nconst u = of (Array) ("x");\n`;
    const r = new InferenceEngine().infer(src);
    const { type } = hoverTypeAt(r, src.indexOf('t = of'));
    expect(prettyTypeToString(type!)).toBe('a -> [a]');
  });
});

// ---------------------------------------------------------------------------
// 2. Phase B + C + D: built-in `.constructor` access typing, Array call-site
//    union widening, and `Function(...)` smart-infer from string args.
// ---------------------------------------------------------------------------

describe('built-in `.constructor` access + widening + Function smart-infer', () => {
  let engine: InferenceEngine;

  beforeEach(() => {
    resetTypeVarCounter();
    clearDataTypes();
    clearCustomMethods();
    engine = new InferenceEngine();
  });

  const noErr = (r: any) =>
    r.diagnostics.filter((d: any) => d.severity !== 3 && !d.message.includes('Unused'));

  const typeOf = (r: any, name: string): string =>
    prettyTypeToString(r.topLevelBindings.get(name).type);

  describe('built-in `.constructor` literal-form access', () => {
    test('`[].constructor` is the Array constructor signature', () => {
      const r = engine.infer(`const ac = [].constructor;`);
      expect(noErr(r)).toEqual([]);
      expect(typeOf(r, 'ac')).toBe('(..., Number | a) -> [a]');
    });

    test('`"".constructor` is `a -> String`', () => {
      const r = engine.infer(`const sc = "".constructor;`);
      expect(noErr(r)).toEqual([]);
      expect(typeOf(r, 'sc')).toBe('a -> String');
    });

    test('`(0).constructor` is `a -> Number`', () => {
      const r = engine.infer(`const nc = (0).constructor;`);
      expect(noErr(r)).toEqual([]);
      expect(typeOf(r, 'nc')).toBe('a -> Number');
    });

    test('`true.constructor` is `a -> Boolean`', () => {
      const r = engine.infer(`const bc = true.constructor;`);
      expect(noErr(r)).toEqual([]);
      expect(typeOf(r, 'bc')).toBe('a -> Boolean');
    });
  });

  describe('Array constructor call widening', () => {
    test('uniform numbers → [Number]', () => {
      const r = engine.infer(`const ac = [].constructor; const xs = ac(1, 2);`);
      expect(noErr(r)).toEqual([]);
      expect(typeOf(r, 'xs')).toBe('[Number]');
    });

    test('mixed string + number → [String | Number]', () => {
      const r = engine.infer(`const ac = [].constructor; const xs = ac("1", 2);`);
      expect(noErr(r)).toEqual([]);
      expect(typeOf(r, 'xs')).toBe('[Number | String]');
    });

    test('direct member call also widens', () => {
      const r = engine.infer(`const xs = [].constructor("a", 1, true);`);
      expect(noErr(r)).toEqual([]);
      expect(typeOf(r, 'xs')).toBe('[Boolean | Number | String]');
    });
  });

  describe('`this.constructor` inside prototype method', () => {
    test('typed as Array constructor when receiver is Array a', () => {
      const src = `
const natives = {};
// natives.Array :: Array a ~> Array a -> Boolean
natives.Array = function (other) {
  const buh = other.constructor;
  return this.length === other.length;
};
`;
      const r = engine.infer(src);
      expect(noErr(r)).toEqual([]);
      // Walk to find `buh` declaration — it's a const inside the function body,
      // not a top-level binding.  Easiest check: scan nodeTypes for the
      // `other.constructor` MemberExpression result.
      const propOffsets = [...(r as any).nodeTypes.keys()] as number[];
      const propStr = '.constructor';
      const idx = src.indexOf(propStr);
      expect(idx).toBeGreaterThan(0);
      // The property identifier starts after the dot.
      const propIdentStart = idx + 1;
      const entry = (r as any).nodeTypes.get(propIdentStart);
      expect(entry).toBeDefined();
      // Mirror hover: scrub the rigid body skolems back to the annotation letters.
      const t = scrubSkolems((engine as any).subst.apply(entry.type), (engine as any).skolemDisplayNames);
      expect(prettyTypeToString(t)).toBe('(..., a | Number) -> [a]');
      expect(propOffsets.length).toBeGreaterThan(0);
    });
  });

  describe('Function constructor smart-infer', () => {
    test('`new Function("a", "b", "return a + b")` infers 2-arg numeric add', () => {
      const r = engine.infer(`const f = new Function("a", "b", "return a + b");`);
      expect(noErr(r)).toEqual([]);
      // The body `a + b` constrains a and b to Number (binary +).  Result is
      // a curried 2-arg numeric function.
      const t = typeOf(r, 'f');
      // Accept any of the equivalent shapes the engine may produce.
      expect(t).toMatch(/Number -> Number -> Number|\(Number, Number\) -> Number/);
    });

    test('`new Function("return 42")` infers `() -> Number`', () => {
      const r = engine.infer(`const f = new Function("return 42");`);
      expect(noErr(r)).toEqual([]);
      const t = typeOf(r, 'f');
      expect(t).toMatch(/\(\) -> Number|Number/);
    });

    test('parse failure falls back without crashing', () => {
      const r = engine.infer(`const f = new Function("not valid (((");`);
      // Should not throw; type is the fallback Function constructor shape or Function.
      expect(() => typeOf(r, 'f')).not.toThrow();
    });
  });
});

// ---------------------------------------------------------------------------
// 3. Fase 1 (#4/#7): a single BUILT-IN container owner for a method name is
//    not sufficient evidence to coerce an unconstrained type variable into
//    that container.  Previously, `x => x.<method>` would pin `x` to `[a]`
//    whenever the built-in Array was the sole registered owner of `<method>`
//    — mis-inferring user values (e.g. a `Right` carrying `map`) as arrays.
//    User-defined sole owners remain a valid structural source.
// ---------------------------------------------------------------------------

describe('built-in sole owner does not coerce an unconstrained receiver', () => {
  let engine: InferenceEngine;

  beforeEach(() => {
    resetTypeVarCounter();
    clearDataTypes();
    clearCustomMethods();
    engine = new InferenceEngine();
  });

  test('precondition: `reduce` is owned only by the built-in Array', () => {
    const owners = findMethodCandidates('reduce').map(([n]) => n);
    expect(owners).toEqual(['Array']);
  });

  test('`x => x.reduce` keeps the parameter polymorphic (not pinned to Array)', () => {
    const r = engine.infer(`const f = (x) => x.reduce;`);
    const t = typeToString(r.type);
    // No Array structure must leak into the inferred parameter type.
    expect(t).not.toContain('[');
    expect(t).not.toContain('Array');
  });

  test('annotated parameter still drives the mismatch check (contrast case)', () => {
    // Accessing `pair.fst` no longer coerces an unannotated parameter to
    // `Pair` (field access does not imply the nominal owner).  Here `pair` is
    // annotated (`Box.fromPair :: Pair a b -> Box b`), so its parameter type is
    // bound from the annotation and the mismatched return (`Box b` vs `Box a`)
    // is still detected.
    const r = engine.infer(`
// Pair :: (a, b) -> Pair a b
// Pair#fst :: Pair a b ~> a
const Pair = (fst, snd) => ({ fst, snd });
// Box :: a -> Box a
const Box = (value) => ({ value });
// Box.fromPair :: Pair a b -> Box b
Box.fromPair = pair => Box(pair.fst);
    `);
    // The mismatched return annotation (Box b vs Box a) is still detected,
    // proving annotation-driven parameter binding remains intact.
    expect(r.diagnostics.length).toBeGreaterThan(0);
  });
});

// ---------------------------------------------------------------------------
// 4. Parametrized smoke-tests for builtin namespace/type methods registered
//    in the method registry.  Each row asserts that a given source snippet
//    type-checks with no error diagnostics AND (optionally) that a named
//    binding receives the expected pretty-printed type.
// ---------------------------------------------------------------------------

describe('builtin namespace/type methods — breadth coverage', () => {
  let engine: InferenceEngine;

  beforeEach(() => {
    resetTypeVarCounter();
    clearDataTypes();
    clearCustomMethods();
    engine = new InferenceEngine();
  });

  const noErr = (r: ReturnType<InferenceEngine['infer']>) =>
    r.diagnostics.filter(d => d.severity !== 3 && !d.message.includes('Unused'));

  interface Case {
    desc: string;
    src: string;
    /** optional [binding, expectedPrettyType] check */
    binding?: [string, string];
  }

  const runCase = ({ src, binding }: Case) => {
    const r = engine.infer(src);
    expect(noErr(r)).toHaveLength(0);
    if (binding) {
      const [name, ty] = binding;
      expect(prettyTypeToString(r.topLevelBindings.get(name)!.type)).toBe(ty);
    }
  };

  const asEach = (cases: Case[]): [string, Case][] =>
    cases.map(c => [c.desc, c]);

  describe('Number statics', () => {
    test.each(asEach([
      { desc: 'Number.isInteger',     src: 'const x = Number.isInteger(1);',      binding: ['x', 'Boolean'] },
      { desc: 'Number.isFinite',      src: 'const x = Number.isFinite(1);',       binding: ['x', 'Boolean'] },
      { desc: 'Number.isNaN',         src: 'const x = Number.isNaN(1);',          binding: ['x', 'Boolean'] },
      { desc: 'Number.isSafeInteger', src: 'const x = Number.isSafeInteger(1);',  binding: ['x', 'Boolean'] },
      { desc: 'Number.parseFloat',    src: 'const x = Number.parseFloat("1.5");', binding: ['x', 'Number'] },
      { desc: 'Number.parseInt',      src: 'const x = Number.parseInt("10");',    binding: ['x', 'Number'] },
    ]))('%s', (_d, c) => runCase(c));
  });

  describe('Math statics', () => {
    test.each(asEach([
      { desc: 'Math.abs',   src: 'const x = Math.abs(-1);',    binding: ['x', 'Number'] },
      { desc: 'Math.max',   src: 'const x = Math.max(1, 2);',  binding: ['x', 'Number'] },
      { desc: 'Math.min',   src: 'const x = Math.min(1, 2);',  binding: ['x', 'Number'] },
      { desc: 'Math.floor', src: 'const x = Math.floor(1.5);', binding: ['x', 'Number'] },
      { desc: 'Math.ceil',  src: 'const x = Math.ceil(1.5);',  binding: ['x', 'Number'] },
      { desc: 'Math.round', src: 'const x = Math.round(1.5);', binding: ['x', 'Number'] },
      { desc: 'Math.sqrt',  src: 'const x = Math.sqrt(4);',    binding: ['x', 'Number'] },
      { desc: 'Math.pow',   src: 'const x = Math.pow(2, 3);',  binding: ['x', 'Number'] },
      { desc: 'Math.log1p', src: 'const x = Math.log1p(3);',   binding: ['x', 'Number'] },
      { desc: 'Math.expm1', src: 'const x = Math.expm1(1);',   binding: ['x', 'Number'] },
      { desc: 'Math.tanh',  src: 'const x = Math.tanh(0.5);',  binding: ['x', 'Number'] },
      { desc: 'Math.LOG10E', src: 'const x = Math.LOG10E;',    binding: ['x', 'Number'] },
      { desc: 'Math.log',   src: 'const x = Math.log(1);',     binding: ['x', 'Number'] },
      { desc: 'Math.sin',   src: 'const x = Math.sin(0);',     binding: ['x', 'Number'] },
      { desc: 'Math.imul',  src: 'const x = Math.imul(3, 4);', binding: ['x', 'Number'] },
    ]))('%s', (_d, c) => runCase(c));
  });

  describe('Date UTC setters', () => {
    test.each(asEach([
      { desc: 'Date#setUTCMonth', src: 'const d = new Date(0); const x = d.setUTCMonth(d.getUTCMonth() + 3);', binding: ['x', 'Number'] },
      { desc: 'Date#setUTCDate',  src: 'const d = new Date(0); const x = d.setUTCDate(1);', binding: ['x', 'Number'] },
      { desc: 'Date#setUTCHours', src: 'const d = new Date(0); const x = d.setUTCHours(12);', binding: ['x', 'Number'] },
    ]))('%s', (_d, c) => runCase(c));
  });

  describe('JSON statics', () => {
    test.each(asEach([
      { desc: 'JSON.stringify', src: 'const x = JSON.stringify({ a: 1 });', binding: ['x', 'String'] },
      { desc: 'JSON.parse',     src: 'const x = JSON.parse("1");' },
    ]))('%s', (_d, c) => runCase(c));
  });

  describe('Date statics', () => {
    test.each(asEach([
      { desc: 'Date.now',   src: 'const x = Date.now();',         binding: ['x', 'Number'] },
      { desc: 'Date.parse', src: 'const x = Date.parse("2025");', binding: ['x', 'Number'] },
      { desc: 'Date.UTC',   src: 'const x = Date.UTC(2025, 0);' },
    ]))('%s', (_d, c) => runCase(c));
  });

  describe('Array statics', () => {
    test.each(asEach([
      { desc: 'Array.isArray', src: 'const x = Array.isArray([1]);', binding: ['x', 'Boolean'] },
      { desc: 'Array.of',      src: 'const x = Array.of(1, 2);' },
      { desc: 'Array.from',    src: 'const x = Array.from([1, 2]);', binding: ['x', '[Number]'] },
      { desc: 'Array.from (Map#values)', src: '// m :: Map String Number\nconst m = new Map();\nconst x = Array.from(m.values());', binding: ['x', '[Number]'] },
      { desc: 'Array.from (Set)', src: 'const s = new Set(["a"]);\nconst x = Array.from(s);', binding: ['x', '[String]'] },
      { desc: 'Array.from (Map entries)', src: '// m :: Map String Number\nconst m = new Map();\nconst x = Array.from(m);', binding: ['x', '[(String, Number)]'] },
      { desc: 'Array.from (string)', src: 'const x = Array.from("abc");', binding: ['x', '[String]'] },
      { desc: 'Array.from (map form)', src: 'const x = Array.from([1, 2], (n, i) => String(n + i));', binding: ['x', '[String]'] },
      { desc: 'Array#splice (insert)', src: 'const xs = [1, 2];\nconst x = xs.splice(1, 0, 5);', binding: ['x', '[Number]'] },
      { desc: 'Array#splice (remove)', src: 'const xs = [1, 2];\nconst x = xs.splice(1);', binding: ['x', '[Number]'] },
      { desc: 'Array.from ({ length })', src: 'const x = Array.from({ length: 3 }, (_u, i) => i * 2);', binding: ['x', '[Number]'] },
    ]))('%s', (_d, c) => runCase(c));
  });

  describe('ES2023 Array copy methods', () => {
    test.each([
      ['toSorted((a, b) => a - b)', '[12.5, 9.95, 30]', '[Number]'],
      ['toSorted()', '["B", "A"]', '[String]'],
      ['toReversed()', '["A", "B"]', '[String]'],
      ['toSpliced(1, 1, "C", "D")', '["A", "B"]', '[String]'],
      ['toSpliced(1)', '["A", "B"]', '[String]'],
      ['toSpliced()', '["A", "B"]', '[String]'],
      ['with(-1, 10)', '[12.5, 9.95]', '[Number]'],
    ])('Array#%s infers the array element type', (call, values, expected) => {
      const r = engine.infer(`const values = ${values}; const result = values.${call};`);
      expect(noErr(r)).toEqual([]);
      expect(prettyTypeToString(r.topLevelBindings.get('result')!.type)).toBe(expected);
    });

    test.each([
      ['with("0", 1)', "Cannot unify 'String' with 'Number'"],
      ['toSorted((a, b) => "first")', "with '(Number, Number) -> String'"],
    ])('Array#%s reports an argument type error', (call, message) => {
      const r = engine.infer(`const prices = [12.5, 9.95]; prices.${call};`);
      expect(noErr(r).map(d => d.message)).toEqual([expect.stringContaining(message)]);
    });
  });

  describe('Console methods', () => {
    test.each(asEach([
      { desc: 'console.log',   src: 'console.log("hi");' },
      { desc: 'console.warn',  src: 'console.warn("hi");' },
      { desc: 'console.error', src: 'console.error("hi");' },
      { desc: 'console.info',  src: 'console.info("hi");' },
      { desc: 'console.debug', src: 'console.debug("hi");' },
      { desc: 'console.table', src: 'console.table([1]);' },
    ]))('%s', (_d, c) => runCase(c));
  });

  describe('Reflect statics', () => {
    test.each(asEach([
      { desc: 'Reflect.has',     src: 'const x = Reflect.has({a:1}, "a");', binding: ['x', 'Boolean'] },
      { desc: 'Reflect.ownKeys', src: 'const x = Reflect.ownKeys({a:1});' },
      { desc: 'Reflect.get',     src: 'const x = Reflect.get({a:1}, "a");' },
    ]))('%s', (_d, c) => runCase(c));
  });

  describe('Object statics', () => {
    test.each(asEach([
      { desc: 'Object.keys',     src: 'const x = Object.keys({a:1});',  binding: ['x', '[String]'] },
      { desc: 'Object.values',   src: 'const x = Object.values({a:1});' },
      { desc: 'Object.entries',  src: 'const x = Object.entries({a:1});' },
      { desc: 'Object.freeze',   src: 'const x = Object.freeze({a:1});' },
      { desc: 'Object.is',       src: 'const x = Object.is(1, 1);',     binding: ['x', 'Boolean'] },
      { desc: 'Object.isFrozen', src: 'const x = Object.isFrozen({});', binding: ['x', 'Boolean'] },
    ]))('%s', (_d, c) => runCase(c));
  });

  describe('String methods', () => {
    test.each(asEach([
      { desc: 'toUpperCase', src: 'const x = "hi".toUpperCase();',   binding: ['x', 'String'] },
      { desc: 'toLowerCase', src: 'const x = "Hi".toLowerCase();',   binding: ['x', 'String'] },
      { desc: 'trim',        src: 'const x = " a ".trim();',         binding: ['x', 'String'] },
      { desc: 'includes',    src: 'const x = "ab".includes("a");',   binding: ['x', 'Boolean'] },
      { desc: 'startsWith',  src: 'const x = "ab".startsWith("a");', binding: ['x', 'Boolean'] },
      { desc: 'split',       src: 'const x = "a,b".split(",");',     binding: ['x', '[String]'] },
    ]))('%s', (_d, c) => runCase(c));
  });

  describe('Promise methods', () => {
    test.each(asEach([
      { desc: 'Promise.resolve', src: 'const x = Promise.resolve(1);' },
      { desc: 'Promise.reject',  src: 'const x = Promise.reject("err");' },
      { desc: 'Promise.all',     src: 'const x = Promise.all([Promise.resolve(1)]);' },
    ]))('%s', (_d, c) => runCase(c));
  });

});

// ---------------------------------------------------------------------------
// 5. Native JS global types Object/Date/Symbol/BigInt are recognised as
//    first-class method-registry receivers — annotations like
//    `// Object#concat :: Object ~> Object -> Object` must not trigger the
//    orphan-method diagnostic, and the method must be registered against
//    the corresponding TCon name.
// ---------------------------------------------------------------------------

describe('Object/Date/Symbol/BigInt as builtin method receivers', () => {
  let engine: InferenceEngine;

  beforeEach(() => {
    resetTypeVarCounter();
    clearDataTypes();
    clearCustomMethods();
    engine = new InferenceEngine();
  });

  test.each(['Object', 'Date', 'Symbol', 'BigInt'])(
    '%s is recognised as builtin',
    (name) => {
      expect(isBuiltinType(name)).toBe(true);
    },
  );

  test('// Object#concat :: Object ~> Object -> Object produces no orphan diag', () => {
    const SRC = `
// Object#concat :: Object ~> Object -> Object
function concat (other) { return Object.assign ({}, this, other); }
`;
    const r = engine.infer(SRC);
    const orphan = r.diagnostics.filter(d =>
      d.message.includes("has no constructor 'Object'"));
    expect(orphan).toEqual([]);
    expect(getMethodNames('Object')).toContain('concat');
  });

  test('// Date#format :: Date ~> String produces no orphan diag', () => {
    const SRC = `
// Date#format :: Date ~> String
function format () { return this.toISOString (); }
`;
    const r = engine.infer(SRC);
    const orphan = r.diagnostics.filter(d =>
      d.message.includes("has no constructor 'Date'"));
    expect(orphan).toEqual([]);
    expect(getMethodNames('Date')).toContain('format');
  });

  test('clearCustomMethods removes user-added Object methods (no leak)', () => {
    engine.infer(`
// Object#concat :: Object ~> Object -> Object
function concat (other) { return Object.assign ({}, this, other); }
`);
    expect(getMethodNames('Object')).toContain('concat');
    clearCustomMethods();
    expect(getMethodNames('Object')).not.toContain('concat');
  });
});

describe('timer globals (setTimeout / clearTimeout / setInterval / clearInterval)', () => {
  beforeEach(() => resetTypeVarCounter());

  test('cancelable delay idiom (Task-style fork) type-checks cleanly', () => {
    // Realistic idiom from functional task libraries: fork starts a timer
    // and returns a cancel thunk that clears it.
    const src = [
      '// delayed :: Number -> Promise e Number',
      'const delayed = x => new Promise ((res, rej) => {',
      '  const t = setTimeout (() => res (x + 1), 10);',
      '});',
      '',
      '// fork :: Number -> (Number -> ()) -> (() -> ())',
      'const fork = x => res => {',
      '  const t = setTimeout (() => res (x), 5);',
      '  return () => clearTimeout (t);',
      '};',
    ].join('\n');
    const r = new InferenceEngine().infer(src);
    expect(r.diagnostics).toEqual([]);
  });

  test('setInterval handle feeds clearInterval', () => {
    const src = [
      'const tick = cb => {',
      '  const h = setInterval (() => cb (), 1000);',
      '  return () => clearInterval (h);',
      '};',
    ].join('\n');
    const r = new InferenceEngine().infer(src);
    expect(r.diagnostics).toEqual([]);
  });

  test('clearTimeout rejects a non-handle argument', () => {
    // NB: primitives coerce permissively against opaque TCons (pre-existing
    // policy), so the misuse probe uses a structurally incompatible value.
    const r = new InferenceEngine().infer('clearTimeout (() => 1);');
    expect(r.diagnostics.length).toBeGreaterThan(0);
  });

  test('setTimeout rejects a non-callable first argument', () => {
    const r = new InferenceEngine().infer("setTimeout ('boem', 10);");
    expect(r.diagnostics.length).toBeGreaterThan(0);
  });
});
