// A member read on a parameter whose type is still unknown (`s => s.length`)
// is parked until the receiver is known.  When the receiver arrives later
// (the data argument of a curried `map`, an immediate call), the member's real
// type must agree with what the code already demanded of it.  Before, a clash
// there was swallowed, so a wrong annotation was accepted:
//
//   // xs :: [String]
//   const xs = map ((s) => s.length) (["Ada"]);   // no error, xs :: [String]

import { InferenceEngine } from '../../src/infer';
import { prettyTypeToString } from '../../src/hm/types';

const FUNCTOR = `// ::constraint Functor f { f :: { map :: f a ~> (a -> b) -> f b } }
// map :: Functor f => (a -> b) -> f a -> f b
const map = (fn) => (functor) => functor.map (fn);
`;

const errors = (src: string) =>
  new InferenceEngine().infer(src).diagnostics
    .filter((d) => (d.severity ?? 1) === 1)
    .map((d) => d.message);

const typeOf = (src: string, name: string) =>
  prettyTypeToString(new InferenceEngine().infer(src).topLevelBindings.get(name)!.type);

describe('a member read on a later-known receiver is checked', () => {
  test('a wrong annotation on the result of a Functor map is reported', () => {
    const src = `${FUNCTOR}// xs :: [String]\nconst xs = map ((s) => s.length) (["Ada"]);`;
    expect(errors(src)).toEqual(["Type mismatch: Cannot unify 'Number' with 'String'"]);
  });

  test('a record field read through a Functor map is checked too', () => {
    const src = `${FUNCTOR}// xs :: [String]\nconst xs = map ((o) => o.total) ([{ total: 12.5 }]);`;
    expect(errors(src)).toEqual(["Type mismatch: Cannot unify 'Number' with 'String'"]);
  });

  test('an immediately applied callback is checked', () => {
    const src = '// n :: String\nconst n = ((s) => s.length) ("Ada");';
    expect(errors(src)).toEqual(["Type mismatch: Cannot unify 'Number' with 'String'"]);
  });

  test('a later call that expects another type is checked', () => {
    const src = `// shout :: String -> String
const shout = (s) => s.toUpperCase ();
// t :: Number -> String
const t = (x) => shout (((o) => o.n) ({ n: x }));`;
    expect(errors(src)).toEqual(["Type mismatch: Cannot unify 'Number' with 'String'"]);
  });

  test('the error points at the member', () => {
    const src = `${FUNCTOR}// xs :: [String]\nconst xs = map ((s) => s.length) (["Ada"]);`;
    const [d] = new InferenceEngine().infer(src).diagnostics.filter((x) => (x.severity ?? 1) === 1);
    expect(src.slice(d.start, d.end)).toBe('length');
  });
});

describe('what stays as it was', () => {
  test('a correct annotation and an inferred result give no error', () => {
    expect(errors(`${FUNCTOR}// xs :: [Number]\nconst xs = map ((s) => s.length) (["Ada"]);`)).toEqual([]);
    const src = `${FUNCTOR}const xs = map ((s) => s.length) (["Ada"]);`;
    expect(errors(src)).toEqual([]);
    expect(typeOf(src, 'xs')).toBe('[Number]');
  });

  test('a heterogeneous array literal (a union element) stays silent', () => {
    // `[r.probs.home, sel (r)]` is approximated as an array of one element
    // type, so the parked `home` meets `Null | String` from its neighbour.
    // That clash comes from the approximation, not from the code.
    const src = `// Scored :: { probs :: { home :: Number }, s :: String | Null }
// scored :: () -> [Scored]
const scored = () => [];
const test = () => {
  // sel :: Scored -> String | Null
  const sel = (r) => r.s;
  const before = (rows) => rows.map ((r) => [r.probs.home, sel (r)]);
  return before (scored ());
};`;
    expect(errors(src)).toEqual([]);
  });

  test('a member with overloads stays silent (String#split)', () => {
    const src = `// splitOn :: String -> String -> Array String
const splitOn = (separator) => (str) => ((s) => s.split (separator)) (str);`;
    expect(errors(src)).toEqual([]);
  });
});
