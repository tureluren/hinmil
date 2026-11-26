# Changelog

All notable changes to HinMil are listed here. The project follows
[semantic versioning](https://semver.org/).

## 0.2.2 — 2026-11-26

### Fixed

- A wrong annotation on a value that reads a member of a callback parameter
  is now reported. `// xs :: [String]` above
  `const xs = map ((s) => s.length) (["Ada"])` (with
  `map :: Functor f => (a -> b) -> f a -> f b`) was accepted; it now gives
  "Cannot unify 'Number' with 'String'" at `length`. The same holds for an
  immediately applied callback and a later call that expects another type.

## 0.2.1 — 2026-11-26

### Fixed

- Hovers and messages show a fresh row as `...r` (then `r1`, `r2`) instead
  of an internal name such as `...r246`.
- Two field accessors in one pipeline
  (`pipe (filter (propEq (false, "paid")), map (prop ("total")))`) no longer
  report "Cannot unify 'total' with 'paid'": when both records are open, a
  label that is not known yet is no longer guessed from the other record's
  fields.

### Documentation

- HinMil is on Open VSX (VSCodium, Cursor, Windsurf): a badge and a note
  under Getting Started.

## 0.2.0 — 2026-11-25

### Type checking

- `::curried` in `.hm` files: directly above a declaration, it lets that
  function accept its arguments in any grouping (`map (f, xs)`,
  `map (f) (xs)`), as in Ramda.  Misplaced, it is reported as a warning.
  The example project has a `hm-types/ramda.hm` built with it.  In a
  JavaScript file `::curried` is reported (HM5002): there the code shows
  whether a function is curried.
- A curry helper declared in a `.hm` file (`curry :: ((a, b, ...) -> z) ->
  a -> b -> ... -> z`) is recognised as in JavaScript, also through a
  namespace import (`R.curry (…)`).  An annotated function built with it
  (`// add :: Number -> Number -> Number` above `curry (…)`) no longer
  rejects `add (1, 2)`.
- The placeholder: an argument of type `Placeholder` (`subtract (__, 10)`)
  leaves its parameter open.
- `import * as ns`: every `ns.f` is instantiated afresh. A first use of a
  polymorphic export no longer fixes its type for the rest of the file.
- HM6001 (missing annotation) is no longer reported for a point-free
  binding (`const total = pipe (map (prop ("total")), sum)`).  A call that
  wraps one function literal (`curry ((a, b) => …)`) is still asked.
- Reading a field outside an open record adds it to the row while the row
  is still free (a callback next to `prop ("paid")`). A function checked
  against its own annotation keeps its rows fixed.

### Documentation

- README: a "Why HinMil?" section comparing HinMil with TypeScript, JSDoc +
  `checkJs` and Flow, including its limitations.
- README: an animated demo of a type error, its hover and the fix.
- README: a link to the example project, hinmil-example.
- More search keywords and a clearer description on npm and the Marketplace.

### Project

- CONTRIBUTING.md, issue forms for bugs and feature requests, and a pull
  request template.
- Continuous integration: build and tests on Node 18, 20 and 22 for every
  push and pull request.

## 0.1.0 — first release

HinMil type-checks plain JavaScript with Hindley-Milner inference. Types are
written as signatures in ordinary comments (`// add :: (Number, Number) -> Number`);
the files stay plain JavaScript, without a build step.

### VS Code extension

- Diagnostics while you type, with codes (`HM1001`…) and configurable severities.
- Hover with inferred types, completion (including auto-imports), signature
  help, go to definition, find references, rename, document symbols and quick
  fixes.
- Syntax highlighting for annotations in comments and for `.hm` type files.
- Works alongside VS Code's built-in TypeScript extension, or without it.
- Project configuration in `hinmil.config.json`, `hinmil.config.js` or a
  `"hinmil"` key in `package.json`, per folder in a monorepo and per folder in
  a multi-root workspace.

### Command-line checker

- `npx hinmil .` checks a project in CI, with `stylish` or `json` output and
  exit codes for errors (`1`) and failures (`2`).
- Uses the same configuration, inference and diagnostics as the extension.

### Type system

- Records with row polymorphism, tuples, sum types, type classes with
  constraints, higher-kinded types, currying, overloading and narrowing.
- Type information for npm packages through `.hm` sidecar files or inline
  `::` annotations, and built-in types for JavaScript, the DOM, React and
  the Node.js core modules.

See the [README](README.md) for the full documentation.
