# HinMil — Hindley-Milner for JavaScript

[![VS Code Marketplace](https://badgen.net/vs-marketplace/v/hinmil.hinmil)](https://marketplace.visualstudio.com/items?itemName=hinmil.hinmil)
[![npm](https://img.shields.io/npm/v/hinmil)](https://www.npmjs.com/package/hinmil)
[![License: MIT](https://img.shields.io/github/license/tureluren/hinmil)](LICENSE)
[![CI](https://github.com/tureluren/hinmil/actions/workflows/ci.yml/badge.svg)](https://github.com/tureluren/hinmil/actions/workflows/ci.yml)

HinMil is a VS Code extension that type-checks plain JavaScript. You write type
signatures in ordinary comments, and a Hindley-Milner inference engine checks
your code against them while you type. There is no build step and no
transpilation — the files stay plain `.js`.

```javascript
// lineTotal :: (Number, Number) -> Number
const lineTotal = (quantity, unitPrice) => quantity * unitPrice;
```

![A call with a string where a number is expected: HinMil underlines it, the hover shows the type mismatch, and after the fix the hover shows the inferred type total :: Number](images/diagnostics.gif)

On top of the checker sit the editor features you would expect: hover types,
diagnostics, completion, signature help, quick fixes, rename, and an outline
view. The type system itself goes further than you might assume for a
comment-based checker: records with row polymorphism, sum types, type classes
with constraints, higher-kinded types, currying, overloading, and type
narrowing. The sections below cover all of it.

---

## Why HinMil?

If you already write Hindley-Milner signatures in your comments, as the
documentation of Ramda, Sanctuary, Fluture and fantasy-land does, HinMil
turns them into checked types. Your code stays plain JavaScript that runs as
it is.

```javascript
// ::constraint Functor f { f :: { map :: f a ~> (a -> b) -> f b } }

// map :: Functor f => (a -> b) -> f a -> f b
const map = fn => functor => functor.map (fn);

const lengths = map (s => s.length) (["Ada", "Alan"]); // [Number]
const wrong   = map (s => s.length) (42);
// ✗ Type mismatch: Cannot unify 'Number' with 'f a'
```

How it compares to the other ways of getting types into JavaScript:

| | HinMil | TypeScript | JSDoc + `checkJs` | Flow |
|---|---|---|---|---|
| Files stay plain `.js`, no build step | yes | no: `.ts` is compiled or stripped | yes | only with its `/*: T */` comment syntax |
| How you write a type | one HM line above the declaration | inline annotations | `@param`, `@returns`, `@template` tags | inline annotations |
| Inference without annotations | Hindley-Milner: `compose = (f, g) => x => f (g (x))` gets `(a -> b, c -> a) -> c -> b` | local; an unannotated parameter is `any` | as TypeScript | local; exports need annotations |
| Curried functions (`a -> b -> c`) | the natural form | possible, verbose with generics | verbose | possible, verbose |
| Higher-kinded types and type classes (`Functor f =>`) | yes | no, only through encodings | no | no |
| Sum types | `Maybe :: Just a \| Nothing`, with constructors and narrowing | discriminated unions | as TypeScript | disjoint unions |
| Types for npm packages | React, Node built-ins, and packages that ship HM annotations; everything else is `Any` | nearly every package (DefinitelyTyped) | as TypeScript | flow-typed, fewer |
| Editors | VS Code, plus a CLI for CI | every major editor | every major editor | most editors |
| Maturity | new (0.x) | very mature | very mature | mature, mostly used at Meta |

**When to choose what:**

- **TypeScript** when you need the ecosystem: types for every dependency,
  editor support everywhere, refactorings, and a team that already knows it.
- **JSDoc + `checkJs`** when you want TypeScript's checker without a build
  step and do not mind the verbose tag syntax.
- **HinMil** when you write JavaScript in a functional style (currying,
  composition, algebraic data types, fantasy-land type classes) and want the
  signatures you already write to be checked, without leaving plain `.js`.

**Honest limitations:**

- A package without HM annotations is `Any`, and `Any` fits everywhere. A
  check is only as strict as the types it can see.
- Inference is strongest on functions and records. A method call on an
  unannotated parameter (`items => items.reduce (…)`) stays open, so annotate
  the functions you export.
- HinMil checks; it never changes or emits code. It is young, has one
  maintainer, and the editor integration is VS Code only.

---

## Table of Contents

- [Why HinMil?](#why-hinmil)
- [Getting Started](#getting-started)
- [Type Annotations](#type-annotations)
  - [Method Annotations](#method-annotations)
- [Hover](#hover)
- [Diagnostics](#diagnostics)
- [Autocompletion](#autocompletion)
- [Signature Help](#signature-help)
- [Code Actions](#code-actions)
- [Go to definition](#go-to-definition)
  - [Using HinMil without the built-in TypeScript extension](#using-hinmil-without-the-built-in-typescript-extension)
- [Find References & Rename](#find-references--rename)
- [Document Symbols](#document-symbols)
- [Syntax Highlighting](#syntax-highlighting)
- [Sum Types](#sum-types)
  - [Variants and constructors](#variants-and-constructors)
  - [Variant methods](#variant-methods)
  - [Factory functions instead of classes](#factory-functions-instead-of-classes)
  - [Multi-line declarations and complex fields](#multi-line-declarations-and-complex-fields)
  - [Phantom variant parameters](#phantom-variant-parameters)
  - [Narrowing on variants](#narrowing-on-variants)
- [JSX & React](#jsx--react)
  - [Optional props](#optional-props)
- [Directives](#directives)
  - [::constraint — Type Classes](#constraint--type-classes)
  - [::narrow — Type Predicates](#narrow--type-predicates)
  - [::types — Cross-File Types](#types--cross-file-types)
  - [::global — Extend Built-in Types](#global--extend-built-in-types)
  - [::prefer — Disambiguate Overlapping Imports](#prefer--disambiguate-overlapping-imports)
  - [::extend — Extend a Type Alias](#extend--extend-a-type-alias)
  - [::rep — Constraint Representatives](#rep--constraint-representatives)
  - [::curried — Curried Library Functions](#curried--curried-library-functions)
  - [::hidden / ::private — Completion Visibility](#hidden--private--completion-visibility)
  - [::ignore / ::ignore-file / ::ignore-function](#ignore--ignore-file--ignore-function)
- [Type System](#type-system)
  - [Primitives](#primitives)
  - [Calling Convention](#calling-convention)
  - [Functions](#functions)
  - [Arrays & Tuples](#arrays--tuples)
  - [Records & Row Polymorphism](#records--row-polymorphism)
  - [Union & String-Literal Types](#union--string-literal-types)
  - [Generics & Higher-Kinded Types](#generics--higher-kinded-types)
  - [Label Polymorphism](#label-polymorphism)
  - [Type Aliases](#type-aliases)
  - [Properties & Private Members](#properties--private-members)
  - [Instance-Callable Values](#instance-callable-values)
  - [Overloading](#overloading)
  - [Picked Projection](#picked-projection)
  - [Curry](#curry)
  - [Pipe & Compose](#pipe--compose)
  - [Type Narrowing](#type-narrowing)
- [Publishing types for an npm package](#publishing-types-for-an-npm-package)
  - [1. Inline annotations (zero config)](#1-inline-annotations-zero-config)
  - [2. Sidecar .hm files](#2-sidecar-hm-files)
  - [3. Package globals](#3-package-globals)
  - [Merge order](#merge-order)
  - [Cross-package chaining](#cross-package-chaining)
- [Using a typed npm package (consumer side)](#using-a-typed-npm-package-consumer-side)
  - [When signatures don't show up](#when-signatures-dont-show-up)
  - [Ramda](#ramda)
- [Built-in Method Types](#built-in-method-types)
  - [Array Methods](#array-methods)
  - [String Methods](#string-methods)
  - [Object Static Methods](#object-static-methods)
  - [Promise Methods](#promise-methods)
  - [Map Methods](#map-methods)
  - [Set Methods](#set-methods)
- [Configuration](#configuration)
  - [Configuration per folder (monorepos)](#configuration-per-folder-monorepos)
  - [Enabling / disabling the language server](#enabling--disabling-the-language-server)
  - [Project-file settings](#project-file-settings)
- [Command-Line Checker](#command-line-checker)
- [Diagnostic Codes Reference](#diagnostic-codes-reference)
- [Example: Full Workflow](#example-full-workflow)
- [License](#license)

---

## Getting Started

1. Install the **HinMil** extension in VS Code.
2. Open any `.js` or `.jsx` file.
3. Add type annotations in comments using `::` syntax:

```javascript
// lineTotal :: (Number, Number) -> Number
const lineTotal = (quantity, unitPrice) => quantity * unitPrice;
```

That is the whole setup. The language server activates on the first JS file
you open and checks as you type.

To see it working first, clone
[hinmil-example](https://github.com/tureluren/hinmil-example): a few small
files, each with one deliberate type error, ready to open in VS Code.

Next steps, all optional:

- **A project configuration** (`hinmil.config.json`, or `"hinmil"` in
  `package.json`) for shared type aliases (`globals`), diagnostic levels and
  file selection — see [Configuration](#configuration). In a monorepo, each
  application folder can have its own.
- **The command-line checker** for CI: `npm install --save-dev hinmil`, then
  `npx hinmil .` — see [Command-Line Checker](#command-line-checker).
- **VS Code's built-in TypeScript extension** also analyses JavaScript and
  shows its own hovers and diagnostics next to those of HinMil. See
  [Using HinMil without the built-in TypeScript extension](#using-hinmil-without-the-built-in-typescript-extension).

---


## Type Annotations

Annotations are written in comments directly above declarations, using `::` to introduce the type signature:

```javascript
// applyVat :: (Number, Number) -> Number
const applyVat = (amount, rate) => amount * (1 + rate);

// identity :: a -> a
const identity = (x) => x;

// invoiceTotal :: [Number] -> Number
const invoiceTotal = (amounts) => amounts.reduce((a, b) => a + b, 0);
```

An annotation (or a directive) takes the **whole** comment line: text after
the type is read as part of it. Put a remark on a line of its own, above:

```javascript
// Gross amount, rounded to cents:
// grossOf :: Number -> Number
const grossOf = (net) => Math.round (net * 1.21);
```

Block comments work too, also over several lines (the annotation runs to
the end of its paragraph, so a long signature can be wrapped):

```javascript
/* invoiceTotal ::
     ([{ quantity :: Number, unitPrice :: Number }], Number) -> Number */
const invoiceTotal = (lines, vatRate) =>
  lines.reduce ((sum, line) => sum + line.quantity * line.unitPrice, 0) * (1 + vatRate);
```

### Method Annotations

Use `~>` for instance method receivers, and annotate constructors with the type they produce:

```javascript
// Box :: a -> Box a
const Box = (value) => ({
  // Box#value :: Box a ~> a
  value,

  // Box#map :: Box a ~> (a -> b) -> Box b
  map(fn) { return Box(fn(this.value)); },
});

// Box.of :: a -> Box a
Box.of = (value) => Box(value);
```

A constructor annotation declares the type, not its fields: give every
field you read through `this` (or on a value of the type) its own
`Type#field` annotation.

Named method and static annotations can also be placed above any declaration:

```javascript
// Box :: a -> Box a
const Box = (value) => ({
  value,

  map(fn) { return Box(fn(this.value)); },
});

Box.of = (value) => Box(value);

// Box#map :: Box a ~> (a -> b) -> Box b
// Box.of  :: a -> Box a
const boxMap = (fn, box) => Box(fn(box.value));
```

---

## Hover

Hover over an identifier to see its inferred type. This works for variables
(`Number`, `String`, `[Number]`), functions (the full signature), methods
(receiver and parameter types), constrained types
(`Functor f => (a -> b) -> f a -> f b`), and narrowed types inside type guard
branches — hovering the same variable in different branches shows different
types.

The display style is configurable: `pretty` shows readable variable names
(`a`, `b`, `c`), `raw` shows the internal ones.

---

## Diagnostics

Type errors show up in the editor as you type. The extension reports type
mismatches, infinite types, missing record properties, unbound variables,
syntax errors in annotations, unresolved imports, constraint violations, and
curry arity problems — see the [Diagnostic Codes Reference](#diagnostic-codes-reference)
for the full list.

```javascript
// applyVat :: (Number, Number) -> Number
const applyVat = (amount, rate) => amount * (1 + rate);

applyVat("21%", 0.21); // Cannot unify String with Number
```

Every diagnostic category can be set to error, warning, information, hint, or
off — see [Configuration](#configuration).

---

## Autocompletion

Completions are driven by the inferred types, so the suggestions after a dot
are the methods that actually exist for that type. This covers identifiers in
scope, methods and properties after `.`, import specifiers from other files,
destructuring patterns, and registered methods inside sumtype factory
functions.

```javascript
const amounts = [120.5, 89.99, 42];
amounts.  // ← suggests: map, filter, reduce, find, length, ...
```

Each completion item shows the inferred type in the detail panel.

---

## Signature Help

When calling a function, the expected parameter types appear with the current
parameter highlighted:

```javascript
// applyVat :: (Number, Number) -> Number
const applyVat = (amount, rate) => amount * (1 + rate);

applyVat(100, |)  // ← shows: applyVat(Number, Number) -> Number
//                           with the second Number highlighted
```

Works with multi-line calls and nested function invocations.

---

## Code Actions

Quick fixes available via the lightbulb menu or `Ctrl+.`:

| Action | Description |
|--------|-------------|
| **Add missing annotation** | Generates an inferred `::` type signature for functions without one |
| **Rename to match annotation** | Fixes name mismatches between annotation and declaration |
| **Add ::types directive** | Suggests importing types from other files |
| **Add constraint to the enclosing signature** | When a call needs a constraint the enclosing function does not declare (`Missing constraint 'Monoid (f a)' required here`), adds it to that function's annotation |
| **Ignore line** | Adds `// ::ignore` to suppress diagnostics on the next line |
| **Ignore file** | Adds `// ::ignore-file` to suppress all diagnostics in the file |

---

## Go to definition

- **Types and annotations** — a type name in an annotation (or a `::narrow` / `::constraint` directive) jumps to its alias, constructor or constraint declaration: in the file, in `globals.hm`, or in a package's `.hm` sidecar. A function name in its own annotation jumps to the code. A `::types` path jumps to the file.
- **Code** (setting `hinmil.navigation.definitions`):
  - a module path jumps to the file: `import … from "x"`, `export … from "x"`, `require ("x")`, `require.resolve ("x")`, `import ("x")`;
  - an imported name jumps to its real declaration, from the import statement and from every use: ESM default, named (also `"string" as name`) and namespace imports (`ns.x`), CommonJS `require` (whole module, destructured, `require ("x").y`), Babel's `_interopRequireDefault (require ("x"))`, `await import ("x")`;
  - re-exports are followed until the declaration: `export { x }`, `export { x as y } from`, `export *`, `export * as ns`, `module.exports = require ("x")`;
  - in the target module it understands `export const/function/class`, `export default`, `module.exports = value`, `module.exports = { a, b: c }`, `exports.a = …`, `module.exports = X; X.a = …`, and `Object.defineProperty (exports, "a", …)`;
  - modules resolve like Node: relative paths with or without extension (`.js`, `.mjs`, `.cjs`, `.jsx`) or `/index`, packages via `exports`, `main`/`module` and subpaths. A package with an `.hm` sidecar opens its JavaScript, not the sidecar;
  - names declared in the same file jump to their binding (scope-aware, like Find References).

  With `auto` (default) HinMil does this only when VS Code's built-in **TypeScript and JavaScript Language Features** extension is not active, so you never get the same result twice. AMD (`define ([…], function (…) {})`) is not supported.

  The clicked text is one link: a whole module path (`"../../services/users"`) or a whole identifier, not one link per word.

### Using HinMil without the built-in TypeScript extension

VS Code ships a built-in extension, **TypeScript and JavaScript Language Features**, that also analyses JavaScript. Next to HinMil it adds a second hover, its own (TypeScript) diagnostics and completions, and suggestions that do not know HM annotations. In a project that relies on HinMil you can switch it off for that workspace only:

1. Open the Extensions view (`Ctrl+Shift+X`, macOS `Cmd+Shift+X`).
2. Type `@builtin typescript` in the search box. Alternatively, run **Extensions: Show Built-in Extensions** from the Command Palette and scroll to the *Features* group.
3. On **TypeScript and JavaScript Language Features**, click the gear icon and choose **Disable (Workspace)**.
4. Reload the window (**Developer: Reload Window**).

Turn it back on the same way with **Enable (Workspace)**.

Good to know:

- **HinMil notices the change.** With `hinmil.navigation.definitions: "auto"` (default), HinMil takes over go to definition for module paths, imported names and local names as soon as the extension is disabled, and hands it back when you enable it again. No setting needs to change.
- **The choice is stored per workspace in VS Code itself**, not in `.vscode/settings.json`. You cannot commit it: every team member who wants this does the steps above.
- **It also switches off TypeScript support for `.ts`/`.tsx` files** in that workspace. Do not do this in a workspace that also contains TypeScript code you want to edit.
- **What you lose:** features only the TypeScript extension offers, such as Find References and Rename across files (HinMil does both within one file), updating imports when you move a file, Organize Imports, refactorings (extract function, …), workspace symbol search (`Ctrl+T`), call hierarchy, inlay hints and its formatter. HinMil still provides hover, diagnostics, completion (including auto-imports), signature help, go to definition, document symbols and code actions.
- **A lighter alternative:** keep the extension and only silence its diagnostics with `"js/ts.validate.enabled": false` (older VS Code versions: `"javascript.validate.enable": false`) in `.vscode/settings.json`. You keep all TypeScript features, but also its hover and completions next to those of HinMil.

---

## Find References & Rename

- **Find All References** — locates every use of an identifier, accounting for scope and shadowing
- **Rename Symbol** — renames across all references in a file, including inside annotations

The engine is scope-aware, so shadowed variables in nested blocks are handled correctly.

---

## Document Symbols

The outline view lists all top-level declarations with their inferred types:

- **Functions** — shown with their full type signature
- **Constructors** — uppercase-named functions displayed as constructors
- **Variables** — non-function declarations
- **Sum type declarations** — shown as enums with variant children

---

## Syntax Highlighting

HM type annotations inside JS comments are syntax-highlighted automatically:

- Type constructors (`Number`, `String`, `Maybe`, etc.)
- Type variables (`a`, `b`, `f`)
- Arrows (`->`, `~>`, `=>`)
- Directive keywords (`::types`, `::constraint`, `::narrow`, `::prefer`, …)

Can be toggled on/off via `hinmil.syntaxHighlighting.enabled`.

![Typing HinMil annotations in VS Code: the signatures in the comments are highlighted as types while you type](images/highlighting.gif)

---

## Sum Types

Sum types (tagged unions, algebraic data types) are a core part of the
type system, and they need no directive. Any annotation whose right-hand
side is a `|`-separated list of capitalised variant names declares one:

```javascript
// Maybe :: Just a | Nothing
```

This registers the type constructor `Maybe a`, links the variants
`Just` and `Nothing` to it, and makes `Maybe` usable in every signature
in the file (or project-wide, via `globals.hm` or `::types`).

### Variants and constructors

The declaration names the variants, but the engine does not guess what
their constructors take — annotate each constructor explicitly. If one
is missing, the engine shows an info diagnostic with the exact
annotation to add (e.g. *"Variant 'Just' is missing a constructor
annotation. Add: `// Just :: a -> Maybe a`"*).

```javascript
// Maybe :: Just a | Nothing

class Just {
  // Just :: a -> Maybe a
  constructor(value) { this.value = value; }

  // Maybe#map :: Maybe a ~> (a -> b) -> Maybe b
  map(fn) { return new Just(fn(this.value)); }
}

// Nothing :: Maybe a
class Nothing {
  map(_fn) { return new Nothing(); }
}
```

Note that both `new Just(1)` and `new Nothing()` are typed as
`Maybe Number` / `Maybe a` — the variant classes construct values of
the *parent* type.

### Variant methods

A method annotated on the parent type (`Maybe#map`) applies to all
variants. Each variant is expected to implement it; a variant that
doesn't gets an info diagnostic (code 6002) on the declaration comment.
Method calls dispatch on the parent type, so a `Maybe Number` value has
`.map` regardless of which variant it holds at runtime.

### Factory functions instead of classes

Classes are not required. A capitalised factory function returning a
record works the same way, and registered methods are offered as
completions inside the returned record literal:

```javascript
// Result :: Ok a | Err e

// Ok :: a -> Result a e
const Ok = (value) => ({
  tag: 'Ok',
  value,
});

// Err :: e -> Result a e
const Err = (error) => ({
  tag: 'Err',
  error,
});
```

### Multi-line declarations and complex fields

Variant fields can be more than bare type variables: parenthesised type
applications and inline record groups are accepted. Long declarations
may span multiple comment lines, joined by a trailing or leading `|`:

```javascript
// Response :: Success { status :: Number, body :: String }
//           | Failure (Object String String)

// Success :: { status :: Number, body :: String } -> Response
// Failure :: (Object String String) -> Response
```

### Phantom variant parameters

A type parameter that a variant does not use stays polymorphic when
that variant is produced. `new Nothing()` is `Maybe a`, not
`Maybe Unknown` — it unifies with whatever `Maybe` the surrounding code
expects:

```javascript
// findDiscount :: Number -> Maybe Number
const findDiscount = (total) =>
  total > 500 ? new Just(total * 0.05) : new Nothing();
```

### Narrowing on variants

Predicates can narrow a value to a single variant via
[`::narrow`](#narrow--type-predicates), and in the negative branch the
type narrows to the union of the remaining variants:

```javascript
// Maybe :: Just a | Nothing
// ::narrow Just
// isJust :: a -> Boolean
const isJust = (m) => m.tag === 'Just';
```

Sum type declarations also show up in the document outline as enums
with their variants as children.

---

## JSX & React

JSX works out of the box in `.js` and `.jsx` files. Detection is
content-based, not extension-based: many modern setups (Vite, Next.js,
create-react-app) keep JSX in plain `.js` files, and those are handled
identically — no configuration, renaming or pragma needed. Imports resolve
across both extensions too (`import App from './App'` finds `App.js`,
`App.jsx` or `index.jsx`).

Every JSX expression
(`<App />`, `<div>…</div>`, `<>…</>`) has the built-in type `ReactElement`,
and a component element is type-checked as a call: `<Greeting name={user} />`
checks the props record `{ name: user }` (plus `children`, when present)
against the component's parameter — a wrong, missing or misspelled prop is
reported on the exact attribute, just like a wrong function argument.

Lowercase host elements (`<div>`, `<button>`) check their attributes against a
builtin DOM catalogue: `className`, `id` and friends must be strings, `style`
must be an object (`style="color:red"` is an error), event handlers
(`onClick`, `onChange`, …) must be functions, and per-tag attributes like
`input`'s `checked` (`Boolean`), `label`'s `htmlFor` or `td`'s `colSpan`
(`Number`) are typed too — with completion for all of them inside the open
tag. Inside `style={{ … }}` the object keys complete against a catalogue of
~170 CSS properties (`color`, `flexDirection`, `gridTemplateColumns`, …);
the values and unknown keys stay unchecked, so CSS custom properties
(`'--brand': …`) and vendor prefixes are always fine. Unknown attribute names
(`data-*`, `aria-*`, web-component attributes) are left
unchecked rather than flagged. React's `key` accepts a `String` or `Number`
and `ref` accepts a ref object or callback ref on any element; both are
React-managed and therefore stripped before a component's props record is
checked, so `<Todo key={it.id} …/>` never complains about an unexpected
`key` field.

React's own API is typed out of the box: the extension bundles signature
files for `react` and `react-dom` ([hm-types-builtin/](hm-types-builtin/)),
so `import { useState } from 'react'` and
`import { createRoot } from 'react-dom/client'` resolve typed signatures
with zero configuration. Two properties keep this future-proof:

- **Your project always wins.** A project `.hm` file for the same package
  (an `overrides` entry or a conventional `hm-types/react.hm`) merges with
  the bundled layer *per export name*: names you declare override the
  bundled signature, names you don't keep working from the bundle. See
  [sample/react.hm](sample/react.hm) for a merge demo that adds React 19
  APIs on top of the bundled catalogue.
- **The bundle can never be worse than no typings.** Importing a name the
  bundled catalogue doesn't know (say React ships a new hook) binds it to
  `Any` instead of erroring — exactly what an untyped package would do.

A larger example — every annotation below is checked against the JSX usage:

```jsx
import { useState, useMemo, createContext, useContext } from 'react';

const ThemeContext = createContext('light'); // Context String

// Badge :: { label :: String } -> ReactElement
const Badge = ({ label }) => <span className="badge">{label}</span>;

// Children arrive as the `children` prop, like in React itself.
// Card :: { title :: String, children :: a } -> ReactElement
const Card = ({ title, children }) => {
  const theme = useContext(ThemeContext); // theme :: String
  return (
    <section className={'card-' + theme}>
      <h2>{title}</h2>
      {children}
    </section>
  );
};

// Todo :: { id :: Number, text :: String, done :: Boolean } -> ReactElement
const Todo = ({ id, text, done }) => (
  <li key={id} className={done ? 'done' : 'open'}>{text}</li>
);

// TodoApp :: { items :: [{ id :: Number, text :: String, done :: Boolean }] } -> ReactElement
const TodoApp = ({ items }) => {
  const [filter, setFilter] = useState('all'); // filter :: String
  const open = useMemo(() => items.filter((it) => !it.done), [items]);

  return (
    <ThemeContext.Provider value="dark">
      <Card title="Tasks">
        <Badge label={filter} />
        {open.length === 0 ? (
          <p>Nothing to do!</p>
        ) : (
          <ul>{open.map((it) => <Todo id={it.id} text={it.text} done={it.done} />)}</ul>
        )}
        <button onClick={() => setFilter('open')}>open only</button>
      </Card>
    </ThemeContext.Provider>
  );
};
```

What gets caught here:

- `<Badge label={3} />` — `Cannot unify 'Number' with 'String'` on the attribute;
- `<Todo id={it.id} />` — `Missing required fields 'text', 'done' on argument`;
- `<ThemeContext.Provider value={42}>` — the Provider's `value` must match the
  context's type (`String` here, fixed by `createContext('light')`);
- `setFilter(1)` — the `useState` setter only accepts a `String` or an updater
  function;
- typos inside braces — `{items.mapp(…)}` — are ordinary member diagnostics.

Spread props type-check like object spreads (`<Todo {...defaults} />`), class
components (`class Timer extends Component`) are instantiated with `new`
behind the scenes, and unannotated components simply get inferred props.

Refs and the modern API are covered by the same bundled typings: the
`useRef(null)` DOM idiom works without complaints (`inputRef.current.focus()`
after mounting), `forwardRef((props, ref) => …)` yields an ordinary component
whose props are still checked, and `createRef`, `useImperativeHandle`,
`useReducer`, `useLayoutEffect`, `useId`, `useTransition`, `useDeferredValue`,
`useSyncExternalStore`, `memo`, `lazy`, `startTransition`, `Suspense` and
`StrictMode` are all typed — see [sample/jsx/refs.jsx](sample/jsx/refs.jsx).

Browser globals — `document`, `window`, `navigator`, `localStorage`,
`sessionStorage` — are typed out of the box: they carry nominal types
(`Document`, `Window`, `Navigator`, `Storage`) with a compact catalogue of
the everyday DOM surface, so `document.getElementById('root')` returns an
`Element`, its members complete and hover, `el.textContent = 42` is caught,
and event listeners see a typed `Event` (`e.clientX`, `e.key`,
`e.target.value`).  Anything *outside* the catalogue silently resolves to
`Any` — the full DOM never false-positives.  The type names are usable in
your own annotations too (`highlight :: Element -> Void`).  Two settings
control this: `hinmil.dom.globalTypes` (default on; turn it off if your
project defines its own `Element`/`Document` types — globals revert to
`Any`) and `hinmil.dom.strictNulls` (default off; when on, lookups that can
miss — `getElementById`, `querySelector`, `getAttribute`,
`localStorage.getItem`, … — return `T | Null`).  A local binding named
`document`, `window`, … still shadows the corresponding browser global
with full strict checking, a declaration in your project globals file
(e.g. `globals.hm`) replaces a builtin entirely, and a
`::global Element#… :: …` directive extends the catalogue per type —
see [sample/browser.js](sample/browser.js).

The Fetch API is typed for every project (browser, node, workers) with no
configuration: `fetch` is `(u, o?) -> Promise e Response`, and `Response`
carries `ok`, `status`, `json()`, `text()`, … — so
`fetch('/api').then(r => r.status.toUpperCase())` is caught.

Other React-ecosystem packages are one `.hm` file away: the same override
mechanism types anything. [sample/redux/](sample/redux/) shows classic
Redux, Redux Toolkit and the react-redux hooks typed by three small
signature files in [sample/hm-types/](sample/hm-types/) — plain packages as
conventional `hm-types/<pkg>.hm` stubs, the scoped `@reduxjs/toolkit` wired
up through an `overrides` entry.

Runnable examples live in [sample/jsx/](sample/jsx/) and
[sample/readme/jsx.jsx](sample/readme/jsx.jsx).

### Optional props

Two conventions are supported, both fully checked:

```jsx
// FP-style: the prop is required, but the value may be Nothing.
// UserBadge :: { name :: String, nickname :: Maybe String } -> ReactElement
const UserBadge = ({ name, nickname }) => (
  <span>{name} ({nickname.getOrElse('no nickname')})</span>
);
const a = <UserBadge name="Ada" nickname={new Just('Countess')} />;
const b = <UserBadge name="Ada" nickname={new Nothing()} />;    // ok
const c = <UserBadge name="Ada" nickname="Countess" />;         // error: String vs Maybe String

// `| Undefined`: the prop may be omitted on the tag entirely.
// Tooltip :: { text :: String, delay :: (Number | Undefined) } -> ReactElement
const Tooltip = ({ text, delay = 300 }) => <span data-delay={delay}>{text}</span>;
const d = <Tooltip text="Save" />;              // ok — delay omitted
const e = <Tooltip text="Save" delay="long" />; // error: String vs Number | Undefined
```

Missing-prop diagnostics carry code `1008` and follow the
`hinmil.diagnostics.missingRecordFields` setting (default `error`). Prop
completion inside an open tag marks `| Undefined` props as `(optional)`.
See [sample/jsx/optional-props.jsx](sample/jsx/optional-props.jsx).

---

## Directives

> All directives use the `::` prefix inside a comment, e.g.
> `// ::constraint …`.

### `::constraint` — Type Classes

Type class constraints come in two flavours:

**Nominal (method dictionary)** — required methods are listed in a
record under the constraint variable:

```javascript
// ::constraint Functor f { f :: { map :: f a ~> (a -> b) -> f b } }
// ::constraint Monad m   { m :: { chain :: m a ~> (a -> m b) -> m b, of :: a -> m a } }
```

**Structural-union (multi-parameter)** — body lists `var :: Type | Type | …`
clauses; satisfied by any value whose type unifies with one of the
alternatives. Multiple header parameters are supported:

```javascript
// ::constraint Runnable t r { r :: (a -> t) | t }
// ::constraint Indexed r e s { r :: [e] | Map s e, s :: Number | String }
```

A constraint builds on constraints declared before it by naming them in its
body (a bare constraint name instead of a record):

```javascript
// ::constraint Pointed f { f :: Functor, f :: { of :: a -> f a } }
// ::constraint Monad m   { m :: Applicative, m :: Chain }
```

A value then has to satisfy the named constraints as well, and a
signature that requires `Pointed f` may use `map` on an `f a`.

Use constraints in signatures with `=>`:

```javascript
// fmap   :: Functor f => ((a -> b), f a) -> f b
// limit  :: Runnable Number r => r -> Limit
```

A full worked example — the constraint is discharged by checking that
the argument's type actually has the required method:

```javascript
// ::constraint Semigroup s { s :: { concat :: s ~> s -> s } }

// joinAll :: Semigroup s => (s, [s]) -> s
const joinAll = (init, xs) => xs.reduce((acc, x) => acc.concat(x), init);

const ref  = joinAll('INV-', ['2026', '-001']); // String has concat — fine
const rows = joinAll([1], [[2], [3]]);          // Array has concat — fine
const bad  = joinAll(5, [6]);
// Type 'Number' does not satisfy constraint 'Semigroup': missing method 'concat'
```

### `::narrow` — Type Predicates

Define type guard functions that narrow types in conditionals. Two
forms are supported:

```javascript
// Narrow to a primitive
// ::narrow String
// isString :: a -> Boolean
const isString = (x) => typeof x === 'string';

// Narrow to a sumtype variant
// Maybe :: Just a | Nothing
// ::narrow Just
// isJust :: a -> Boolean
const isJust = (m) => m.tag === 'Just';
```

Requirements:
- The predicate function must return `Boolean`
- The first parameter must be a type variable (`a`)
- The narrowed type is specified by the `::narrow` directive

In use, both branches narrow. Here `q` is `Number` inside the positive
branch and `String` in the negative one, so both method calls check out:

```javascript
// ::narrow Number
// isCount :: a -> Boolean
const isCount = (x) => Number.isInteger(x) && x >= 0;

// quantityLabel :: (Number | String) -> String
const quantityLabel = (q) => isCount(q) ? q.toFixed(0) : q.trim();
```

`typeof x === 'string' | 'number' | 'boolean' | 'bigint' | 'symbol'`
narrows automatically — no `::narrow` annotation is needed for those.

### `::types` — Cross-File Types

Import type definitions from other files or packages without runtime
imports:

```javascript
// Types from ./demo.js (or ./demo.hm when there is no demo.js):
// ::types ./demo

// Types from an npm package's hinmil sidecar (also scoped: @scope/pkg):
// ::types fantasy-box
```

A `::types` target also brings the `::types` of that file with it, so a
shared `types.js` can itself pull in other type files.

A typical split: keep shared aliases in one file, reference them
everywhere else. Note that `::types` imports *types only* — value
bindings (functions, classes) still need a regular `import`/`require`:

```javascript
// invoice-types.js
// LineItem :: { description :: String, quantity :: Number, unitPrice :: Number }
// VatRate :: Number
```

```javascript
// main.js
// ::types ./invoice-types

// lineTotal :: LineItem -> Number
const lineTotal = (item) => item.quantity * item.unitPrice;

// applyVat :: (Number, VatRate) -> Number
const applyVat = (amount, rate) => amount * (1 + rate);
```

**Types travel with imports.** Importing a value from a JavaScript
module (`import` or `require`) also makes the type names visible in that
module available: its free-standing aliases (`// LineItem :: { … }`, not
attached to a declaration), the targets of its `::types` directives, and,
recursively, the types of its own imports. So you only need `::types`
for type-only use — a file that names `LineItem` but imports nothing
from `invoice-types.js`. When two imports provide the same name, the
nearer one wins; a local declaration always wins. An annotation on a
declaration (`// lineTotal :: LineItem -> Number`) is a value annotation
and is not exported as a type name.

### `::global` — Extend Built-in Types

Despite the name, `::global` does not declare global *variables* — it
registers methods and statics on types (typically prototype extensions
the checker cannot see). The "global" refers to the *reach* of the
declaration: it applies to every file in the project scope that loads it
(the folder with the configuration, and everything below it).
Instance methods use `Type#method` with a `~>` receiver; statics use
`Type.method`:

```javascript
// ::global Array#ap :: [a] ~> [a -> b] -> [b]
// ::global Array.empty :: () -> [a]
```

`::global` is read from your project's globals file(s) (e.g.
`globals.hm`, or whatever `hinmil.globals` points at — see
[Configuration](#configuration)), and the declarations then apply to
every file in the workspace.

### `::prefer` — Disambiguate Overlapping Imports

When two packages export the same name (e.g. both expose `Prop`),
declare which source to prefer in the current file:

```javascript
// Both sqlkit and another dependency publish a `Prop`:
// ::types sqlkit
// ::types other-orm

// ::prefer Prop from sqlkit

// Several names at once:
// ::prefer Prop, Table from sqlkit
```

The directive only affects the file it appears in, so different files
can resolve the same name to different packages.

### `::extend` — Extend a Type Alias

Append alternatives to an existing union alias without redefining it. This is
mainly useful when the alias comes from a package sidecar and you want to
widen it locally (or in an override sidecar):

```javascript
// Selector :: String | Prop a

// ::extend Selector Limit
// Selector is now String | Prop a | Limit
```

String-literal branches work too — handy for widening a status union
that a library defined too narrowly:

```javascript
// PaymentMethod :: 'cash' | 'card'

// ::extend PaymentMethod 'voucher'

// pmLabel :: PaymentMethod -> String
const pmLabel = (m) => m;
const ok = pmLabel('voucher');   // fine — 'voucher' is now part of the union
```

Directives stack — each `::extend` adds further branches. Extending a
non-union alias turns it into a union; extending an unknown name declares a
new alias.

### `::rep` — Constraint Representatives

Declare that a locally annotated method represents a constraint's like-named
method when discharging that constraint. `Type#method` registers an instance
method (with a `~>` receiver), `Type.method` a static one. The signature
must follow directly below the directive.

Useful when a type satisfies a constraint in spirit but the checker cannot
see the method — e.g. `Array` has no built-in `empty`, so a `Monoid`
constraint would reject it:

```javascript
// ::constraint Monoid m { m :: { empty :: () -> m } }

// ::rep Monoid Array.empty
// Array.empty :: () -> Array a

// orEmpty :: Monoid m => m -> m
const orEmpty = (x) => x;

const r = orEmpty([1, 2]);   // fine — without the ::rep this reports:
// Type 'Array' does not satisfy constraint 'Monoid': missing method 'empty'
```

### `::curried` — Curried Library Functions

Only in `.hm` files.  `::curried` directly above a declaration lets that
function take its arguments in any grouping, the way the functions of Ramda
and similar libraries do.  One `::curried` covers the overload lines of the
name below it:

```
// fnkit.hm
::curried
map :: (a -> b) -> [a] -> [b]
map :: (a -> b) -> Object String a -> Object String b
::curried
subtract :: Number -> Number -> Number
negate :: Number -> Number
```

```javascript
map (f, xs);         // all at once
map (f) (xs);        // one at a time
F.map (f, xs);       // through `import * as F from "fnkit"`
```

Without the directive, a curried signature `a -> b -> c` takes one
argument per call, as a plain `a => b => c` does.  A `::curried` that is
not directly above a function of at least two arguments is reported as a
warning in the `.hm` file.

In a JavaScript file `::curried` is reported (HM5002): there the code
shows whether a function is curried.  A function built with a curry helper
accepts any grouping as soon as the helper has a curry signature, also
when the helper comes from a `.hm` file or a namespace import
(`R.curry (…)`), and also when the function carries its own annotation:

```javascript
// discounted :: Number -> Number -> Number
const discounted = curry ((pct, price) => price * (1 - pct / 100));
discounted (10, 250);    // fine
discounted (10) (250);   // fine
```

A hand-written `pct => price => …` really needs one argument per call,
and HinMil keeps checking it that way.

An argument whose type is `Placeholder` (declare `Placeholder ::
Placeholder` and `__ :: Placeholder`) leaves its parameter open:
`subtract (__, 10)` is `Number -> Number`.

### `::hidden` / `::private` — Completion Visibility

Keep a method or property out of completion lists. Place the directive on the
line above the annotation, or use the standalone form with a qualified name:

```javascript
// ::hidden
// Invoice#recalculate :: Invoice ~> () -> ()

// ::hidden Invoice#internalId
// ::private Invoice#cache
```

`::hidden` keeps a member out of every completion list; `::private` keeps it
out too, except after `this.` — inside the type's own methods, where it is
used.
Several directives can be stacked above one chained annotation; a
`::hidden <Name>` argument targets that specific member.

### `::ignore` / `::ignore-file` / `::ignore-function`

Suppress diagnostics selectively:

```javascript
// ::ignore
const x = untypedFunction(42); // diagnostics on the next line are suppressed

// ::ignore-function
const legacy = (a, b) => {
  // no diagnostics anywhere in this function body
};

// ::ignore-file
// Anywhere in a file (usually at the top): no diagnostics in this file
```

`::ignore` suppresses exactly the line **below** the comment, so put it
directly above the code line — below an annotation, not above it:

```javascript
// fee :: Number
// ::ignore
const fee = legacyFee ();
```

`::ignore-function` suppresses the whole function that follows it (an
annotation in between is fine). `::ignore` and `::ignore-file` are also
available as quick fixes on an existing diagnostic (see
[Code Actions](#code-actions)).

---

## Type System

The engine is classic **rank-1 Hindley-Milner** with full inference — no
annotation is ever required for the machinery to work, and inferred types are
principal (most general). On top of that, **rank-N polymorphism is available
opt-in** by writing an explicit `forall` in an annotation:

```javascript
// applyBoth :: (forall a. a -> a) -> (Number, String) -> [Number, String]
const applyBoth = f => (n, s) => [f(n), f(s)];

const ok  = applyBoth(x => x)(1, "one");      // ✓
const bad = applyBoth(x => x + 1)(1, "one");  // ✗ Argument is not polymorphic enough
```

A `forall` parameter is bound as a real scheme in the body and arguments are
checked by skolemization at the call site — including skolem-escape detection,
constraints inside the `forall`, and polymorphic record fields. A `forall` is
never inferred, only checked. Worked examples live in
[sample/rankN/](sample/rankN/); the full design — along with everywhere else
the engine extends or bends the textbook algorithm — is catalogued in
[TYPE-SYSTEM.md](TYPE-SYSTEM.md).

### Primitives

| Type | Description |
|------|-------------|
| `Number` | JavaScript numbers |
| `String` | JavaScript strings |
| `Boolean` | `true` / `false` |
| `Null` | `null` |
| `Undefined` | `undefined` |
| `Void` | No return value |
| `Any` | A value nothing is known about (an import from an untyped package, `globalThis`); fits everywhere |

Numeric refinements in the style of Sanctuary — `Integer`, `PositiveNumber`,
`NegativeNumber`, `NonZeroInteger`, `PositiveInteger`, `NonNegativeInteger`,
`FiniteNumber`, `ValidNumber`, `Float`, `Double`, … — are `Number` to the
type checker. A numeric **literal** passed to such a parameter is checked
against the refinement (`f (2.5)` for `f :: Integer -> …` reports
`'2.5' is not an integer`); other values are not.

### Calling Convention

JavaScript calls are **tuple-applied**: `f(a, b)` constructs `Tuple[A, B]`
and unifies it against the function parameter. So a multi-argument JS
function MUST be annotated in tuple form:

```javascript
// For factory(a, b):
// factory :: (A, B) -> C

// For factory(a)(b) (curried):
// factory :: A -> B -> C
```

This is the single most common source of confusion when authoring
sidecars — see [Curry](#curry) for how curried forms are detected.

### Functions

```javascript
// Single argument
// formatAmount :: Number -> String
const formatAmount = (n) => `€ ${n.toFixed(2)}`;

// Multiple arguments
// applyVat :: (Number, Number) -> Number
const applyVat = (amount, rate) => amount * (1 + rate);

// Higher-order
// map :: ((a -> b), [a]) -> [b]
const map = (fn, xs) => xs.map(fn);
```

An annotation is a promise the body must keep. Type variables are
**rigid** inside the body: the caller chooses them, so the body may not
pick one for them.

```javascript
// second :: (a, b) -> b
const second = (x, y) => x;
// HM1003: 'second' has type '(a, b) -> a' but annotation expects '(a, b) -> b'
```

Type variables are **scoped lexically**, like generics: a letter in a
nested annotation that also appears in the enclosing annotation is the
same variable, so closure helpers can be annotated:

```javascript
// keepWhere :: (a -> Boolean) -> [a] -> [a]
const keepWhere = (keep) => (items) => {
  // The same `a` as in keepWhere:
  // check :: a -> Boolean
  const check = (item) => keep (item);
  return items.filter (check);
};
```

A parameter with a JavaScript default value may be left out at a call
site; the annotation names its type as usual:

```javascript
// padLabel :: (String, Number, String) -> String
const padLabel = (label, width, fill = " ") => label.padEnd (width, fill);

padLabel ("Total", 10);   // fine: `fill` has a default
```

### Arrays & Tuples

```javascript
// Arrays — homogeneous
// invoiceTotal :: [Number] -> Number
const invoiceTotal = (amounts) => amounts.reduce((a, b) => a + b, 0);

// Tuples — fixed-length, heterogeneous: one type per position
// formatLine :: [String, Number] -> String
const formatLine = (line) => `${line[0]}: ${line[1]}`;

formatLine (["Coffee", 3]);   // fine
formatLine ([3, "Coffee"]);   // Cannot unify 'Number' with 'String' (and back)
```

Do not confuse `[A, B]` (one tuple argument) with `(A, B)` (two arguments,
see [Calling Convention](#calling-convention)).

### Records & Row Polymorphism

```javascript
// Record types with named fields
// customerLabel :: { name :: String, vatNumber :: String } -> String
const customerLabel = (customer) => `${customer.name} (${customer.vatNumber})`;
```

Records use **structural typing** — any object with matching fields
satisfies the type.

Use `...rest` to make a record open (extensible):

```javascript
// pickName :: { name :: String, ...rest } -> String
const pickName = (o) => o.name;

// drop :: { x :: a, ...rest } -> { ...rest }
```

Open vs. open records unify their tails through a shared row variable;
closed-vs-closed unification silently accepts extra caller fields for
JS compatibility.

Reading a field that an open record does not list adds it to the row, as
long as that row is still free. A callback typed from a library signature
(`prop :: k -> { [k] :: a, ...r } -> a`) can read other fields this way:

```javascript
// isBigUnpaid :: { total :: Number, paid :: t, ...r } -> Boolean  (inferred)
const isBigUnpaid = both (complement (prop ("paid")), (order) => order.total > 50);
```

A function checked against its own annotation keeps its row fixed: with
`pickName :: { name :: String, ...rest } -> String`, reading `o.title` is
an error.

One exception catches typos: an **object literal** passed where a
**named** closed record (an alias) is expected may not have fields the
alias does not declare. That is reported as HM1010, with a "did you
mean" hint when a declared field is close:

```javascript
// Customer :: { name :: String, vatNumber :: String, email :: String | Undefined }

// customerLabel :: Customer -> String
const customerLabel = (c) => c.name;

customerLabel ({ name: "Acme", vatNumber: "NL001", emial: "info@acme.test" });
// HM1010 Unknown field 'emial' on argument; expected 'Customer' (did you mean 'email'?)
```

Values that are not literals (a record built elsewhere, a destructured
parameter) and inline record types keep the lenient rule.

A computed key is the key's *value*: `{ ["currency"]: "EUR" }` has a field
`currency`, a label variable makes a label field (`k -> a -> { [k] :: a }`),
and a key known only at runtime (`{ [field]: value }` with `field ::
String`) gives a dictionary, `Object String v`, which `Object.assign` and
spreads merge as dictionaries. The level is
set with `diagnostics.excessRecordFields`.

### Union & String-Literal Types

```javascript
// Explicit union
// show :: Number | String -> String
const show = (x) => String(x);

// Automatically inferred from conditionals
const reference = Math.random() > 0.5 ? 2026001 : "draft";
// reference :: Number | String

// Singleton string-literal types
// statusLabel :: 'draft' | 'sent' | 'paid' -> String
const statusLabel = (s) => `status: ${s}`;
```

String literals in type position parse as `TLabel` (a singleton type).
At call sites a literal string must be one of the allowed values, and a
plain `String` does not fit a literal union (it could hold any text):

```javascript
statusLabel ("paid");    // ok
statusLabel ("piad");    // HM1001: 'piad' is not one of 'draft' | 'paid' | 'sent'

// fromInput :: String -> String
const fromInput = (raw) => statusLabel (raw);
// HM1001: 'String' does not fit 'draft' | 'paid' | 'sent'
```

A literal assigned to a `const` keeps its literal type (`const status =
"sent"` fits), and so does a ternary of literals (`paid ? "paid" :
"sent"`).

**Unions have a direction.** An argument must fit the parameter: every
member of a union argument has to be accepted by the parameter, so
`Number | Undefined` does not fit `Number | Null`. The other way round,
a function may return *less* than its annotation promises: a body that
returns `String | Null` satisfies `-> String | Number | Null`, but not
`-> String` (a member it does not declare).

```javascript
// shown :: Number | Null -> String
const shown = (n) => n == null ? "-" : String (n);

// countLabel :: Number | Undefined -> String
const countLabel = (n) => shown (n);
// HM1001: Cannot unify 'Number | Undefined' with 'Null | Number'
```

### Generics & Higher-Kinded Types

Lowercase identifiers are type variables (parametric polymorphism).
Constraint-bound variables can stand for higher-kinded types:

```javascript
// identity :: a -> a
const identity = (x) => x;

// fmap :: Functor f => ((a -> b), f a) -> f b
const fmap = (fn, fa) => fa.map(fn);

// chain :: Monad m => (a -> m b) -> m a -> m b
```

A constraint variable like `f` (declared in the constraint head) parses
greedily — it absorbs juxtaposed atoms (`f a`, `m (Maybe a)`). Plain
non-constraint vars only consume juxtaposition when followed by `(...)`.

Two-parameter constructors work the same way: `QueryTag p o`,
`Either e a`, `Map k v`.

### Label Polymorphism

A computed key — `o[k]`, or destructuring `({ [k]: v }) => v` — infers a
*label variable* (a separate sort from type vars) so accessors can be
polymorphic over field names:

```javascript
// pluck :: (k, { [k] :: a, ...r }) -> a
const pluck = (k, o) => o[k];

pluck("x", { x: 1, y: 2 });   // k := 'x', a := Number
pluck("y", { y: "hi" });      // k := 'y', a := String
```

### Type Aliases

Uppercase top-level names that don't return a constructor are treated
as aliases. Free type variables are recorded and re-instantiated at
each use site:

```javascript
// LineItem :: { description :: String, quantity :: Number, unitPrice :: Number }
// Selector :: String | Prop a | Limit
```

Aliases expand at unification time with cycle detection, and they are
**nominal**: two aliases with the same fields are still different types, so a
`Customer` is not accepted where a `Supplier` is expected. A plain record
(an object literal, an unannotated value) fits any alias whose fields it has.

### Properties & Private Members

Annotate non-method properties (no `~>`) directly:

```javascript
// Invoice#number   :: String
// Invoice#lines    :: [LineItem]
```

Private members (JS `#name` syntax) use a double `##`:

```javascript
// Counter :: () -> Counter
class Counter {
  #count = 0;
  // Counter##count :: Number
  // Counter#tick :: Counter ~> () -> ()
  tick() { this.#count++; }
}
```

### Instance-Callable Values

Annotate values whose runtime values are themselves callable
(parser tag functions, builder factories, etc.):

```javascript
// The constructor:
// SQLTag :: a -> SQLTag a

// Calling an SQLTag instance:
// SQLTag() :: a -> Promise Error [b]
```

The `Type()` form lives in a separate namespace from the constructor;
hovering on a value of that type surfaces only the instance-callable
overloads.

### Overloading

Repeating a top-level decl registers an additional call signature:

```javascript
// total :: Invoice -> Number
// total :: [Invoice] -> Number
```

At each call site, the engine tries each branch in declaration order
and picks the **first** that unifies. A branch only fits when the
arguments fit its parameters [in their direction](#union--string-literal-types):
a plain `String` does not take a `'asc' | 'desc'` branch.

A union argument whose members fit *different* branches is resolved per
member, as it runs, when the results agree:

```javascript
// toPromise :: Promise e a -> Promise e a
// toPromise :: a -> Promise e a
const toPromise = (x) => x instanceof Promise ? x : Promise.resolve (x);

// Outcome :: { ok :: Boolean, field :: String }
// RuleResult :: Outcome | Promise Error Outcome

// passed :: RuleResult -> Promise Error Boolean
const passed = (result) => toPromise (result).then (outcome => outcome.ok);
// Outcome takes the second branch, the promise the first: Promise Error Outcome
```

### Picked Projection

`Picked Row Selectors` is a built-in type constructor that *projects* a
row record at the call site. The introspect-style sidecar declares per-table
overloads like:

```hm
Organisation :: [OrganisationSelector] -> QueryTag p (Picked OrganisationRow OrganisationSelector)
```

When called with a literal-array argument, the LSP narrows `Picked` to
the actual selected fields. Method-shadows on the row type
(`OrganisationRow#locations :: [LocationRow]`) drive nested projection
for relations.

A nested query contributes **what calling it returns**, read off its
type's instance-callable annotation, so a library controls the shape of a
relation by how it types its query values:

```hm
QueryTag() :: p -> Promise e [o]            // nested: a list relation
QueryOne() :: p -> Promise e (o | Null)     // nested: one related row, or null
QueryExists() :: p -> Promise e Boolean     // nested: a filter, adds no field
```

A callable whose result holds the row without an array (`o`, `o | Null`)
also receives the host's row type, like `[o]` does.  A project override in
`hm-types/<pkg>.hm` may replace these callables, e.g. when the project runs
the library's queries through a runner that returns a task:

```hm
QueryTag() :: p -> RTask r Error [o]
```

### Curry

To curry a function, you need a `curry` helper with the right signature. The LSP detects curry wrappers by their annotation pattern — a function that takes a tuple-param function and returns a curried version:

```javascript
// curry :: ((a, b, ...) -> z) -> a -> b -> ... -> z
export const curry = fn => {
  const curried = (...args) => {
    if (args.length >= fn.length) return fn(...args);
    return (...next) => curried(...args, ...next);
  };
  return curried;
};
```

Wrap any multi-param function with `curry()` to enable partial application:

```javascript
// discountedTotal :: (Number, Number, Number) -> Number
const discountedTotal = (quantity, unitPrice, discountPct) =>
  quantity * unitPrice * (1 - discountPct / 100);

const curriedTotal = curry(discountedTotal);
// curriedTotal :: Number -> Number -> Number -> Number
```

All partial application forms are then valid:

```javascript
curriedTotal(2, 50, 10)      // fully applied
curriedTotal(2)(50)(10)      // fully curried
curriedTotal(2, 50)(10)      // partial + apply
curriedTotal(2)(50, 10)      // apply + partial
```

> **Note:** Without wrapping in `curry()`, a function with signature `(a, b, c) -> d` simply expects all arguments at once. The LSP only generates curried overloads when it detects the `curry()` call.

A library whose functions are already curried (Ramda and its relatives) is
described in a `.hm` file with [`::curried`](#curried--curried-library-functions);
see [Ramda](#ramda) for a complete example.

### Pipe & Compose

The LSP supports variadic `pipe` and `compose` functions using **spread tuple syntax** in annotations. It validates that chained functions connect properly — the output of one must match the input of the next.

#### Pipe (left-to-right)

```javascript
// pipe :: ((a -> b), (b -> c), ..., (y -> z)) -> a -> z
const pipe = (...fns) => fns.reduce((acc, fn) => x => fn(acc(x)));

const invoiceLabel = pipe(
  x => x * 1.21,           // Number -> Number   (apply VAT)
  x => x.toFixed(2),       // Number -> String   (format)
  x => `€ ${x}`,           // String -> String   (prefix)
);
// invoiceLabel :: Number -> String
```

The LSP verifies each link in the chain — if the output of one function doesn't match the input of the next, it reports a type error:

```javascript
// withVat :: Number -> Number
const withVat = x => x * 1.21;

// format :: Number -> String
const format = x => x.toFixed(2);

const broken = pipe(format, withVat);
// Cannot unify 'Number' with 'String': format gives a String, withVat wants a Number
```

The links are checked against what is known about each function: an
unannotated lambda such as `x => x * 1.21` is checked leniently (JavaScript
would coerce a String there), so give the steps signatures where the chain
matters.

#### Compose (right-to-left)

```javascript
// compose :: ((y -> z), ..., (b -> c), (a -> b)) -> a -> z
const compose = (...fns) => fns.reduceRight((acc, fn) => x => fn(acc(x)));

const invoiceLabel = compose(
  x => `€ ${x}`,           // String -> String   (prefix)
  x => x.toFixed(2),       // Number -> String   (format)
  x => x * 1.21,           // Number -> Number   (apply VAT)
);
// invoiceLabel :: Number -> String
```

The direction is detected automatically from the annotation — shared type variables between adjacent function positions determine whether the chain flows left-to-right (pipe) or right-to-left (compose).

### Type Narrowing

Types are automatically narrowed inside conditional branches:

```javascript
// typeof guards
if (typeof x === 'string') {
  // x: String
}

// Null checks
if (x != null) {
  // x: narrowed (null/undefined removed)
}

// Truthiness
if (x) {
  // x: narrowed (null/undefined removed)
}

// ::narrow predicates
// ::narrow Number
// isNumber :: a -> Boolean
const isNumber = (x) => typeof x === 'number';

if (isNumber(value)) {
  // value: Number
}
```

A guard that leaves the function narrows the rest of it, and so does a
default that is assigned in the guard:

```javascript
// Customer :: { name :: String, email :: String | Null }

// greeting :: Customer | Null -> String
const greeting = (customer) => {
  if (!customer) return "Hello";
  return "Hello " + customer.name;          // customer: Customer
};

// pageSize :: Number | Null -> Boolean -> Number
const pageSize = (size) => (compact) => {
  if (compact || size == null) return 10;
  return size * 2;                          // size: Number
};

// displayName :: String | Null -> String
const displayName = (name) => {
  if (name == null) name = "guest";
  return name.toUpperCase ();               // name: String
};

// emailOf :: Customer -> String
const emailOf = (customer) => {
  if (customer.email == null) return "-";
  return customer.email.toLowerCase ();     // customer.email: String
};
```

Narrowing follows identifiers and member paths (`customer.email`), not
computed expressions: for `orders[0].customer` bind the value to a
`const` first.

#### Lookups that can miss

`Map#get` returns `v | Undefined`: the key may be absent. Three ways to
handle it:

```javascript
// Fixture :: { id :: Number, team :: Number }

// rates :: Map String Number
const rates = new Map ([["NL", 0.21], ["BE", 0.21]]);

// 1. Check the result.
// vatOrZero :: String -> Number
const vatOrZero = (country) => rates.get (country) ?? 0;

// 2. Check the key first: after `has` on the same map and key, `get`
//    cannot miss (also after `if (!m.has (k)) m.set (k, …);` and after
//    `if (!m.has (k)) return …;`).
// vatOf :: String -> Number
const vatOf = (country) => rates.has (country) ? rates.get (country) : 0;

// groupByTeam :: [Fixture] -> Map Number [Fixture]
const groupByTeam = (fixtures) => {
  const byTeam = new Map ();
  fixtures.forEach (f => {
    if (!byTeam.has (f.team)) byTeam.set (f.team, []);
    byTeam.get (f.team).push (f);
  });
  return byTeam;
};

// 3. State it: you know the key is there (an invariant hinmil cannot see).
// dutchVat :: Number
const dutchVat = rates.get ("NL");
```

The third form works for any `const` whose value comes from a lookup —
a call, a member access or an `await` — that may give `Undefined` or
`Null`: the annotation may leave those out. The rest of the type must
still match (`// dutchVat :: String` is an error), and a value that is
`undefined` by construction (`member ? 10 : undefined`) is still
reported. The map and key of a `has`/`get` pair are compared as paths
(`m`, `this.cache`, `state.byTeam`; `key`, `row.teamId`, `"NL"`): a key
computed by a call (`m.get (keyOf (row))`) needs a `const` first.

---

## Publishing types for an npm package

As a package author you have three independent ways to ship HM signatures
with your code. Pick whichever fits — or mix them. A consumer never has to
configure anything: the LSP discovers your signatures automatically when they
`import` your package.

### 1. Inline annotations (zero config)

Write `// Name :: Type` comments directly above your JS definitions.
No extra files, no `package.json` entry, no build step:

```javascript
// node_modules/mylib/index.js

// limit :: Number -> Limit
exports.limit = (n) => ({ tag: 'limit', n });

// add :: Number -> Number -> Number
exports.add = (a) => (b) => a + b;
```

When a consumer does `import { limit } from 'mylib'`, the LSP
BFS-walks your package starting from `main` / `module`, follows
`import` / `export ... from` / `require` edges, **stays inside the
package root** (no `../` escapes), and collects every inline
signature it finds. The walk is capped at 256 files per package.

Anything that works in source — `::constraint`, sum type declarations,
type aliases, `Type#method`, `Type() ::`, `::types <pkg>` chaining —
works inline too:

```javascript
// node_modules/mylib/index.js
// ::constraint Runnable r { r :: (a -> r) | r }
// Pull in another lib's types too:
// ::types some-other-lib

// runIt :: Runnable r => r -> Limit r
exports.runIt = (r) => ({ tag: 'limit', r });
```

### 2. Sidecar `.hm` files

For authors who prefer to keep types out of the JS source, or version
them separately. Declare them under `"hinmil"` in `package.json`:

```json
{
  "name": "mylib",
  "main": "index.js",
  "hinmil": {
    "sidecars": "./types.hm"
  }
}
```

A sidecar contains the same declarations you would write in-source
(top-level signatures, `Type#method`, `Type.static`, `Type() ::`,
sum type declarations, `::constraint`, type aliases, …) but without
the `// ` comment prefix — it's pure HM source. In a `.hm` file `//`
starts a comment, on a line of its own or after a declaration
(`Status :: 'open' | 'paid'   // as the provider sends it`); `/* … */`
blocks are comments too. Directives are written bare as well
(`::types other-lib`, `::constraint …`): a `// ::types …` line in a
`.hm` file is a comment.

Multiple sidecars are supported; later entries **override** earlier
ones for both value exports and type aliases:

```json
{
  "hinmil": {
    "sidecars": [
      "./sqlkit.hm",
      "../.sqlkit/client/index.hm"
    ]
  }
}
```

Sidecar files are watched: edits trigger transitive cache invalidation
so downstream files re-check immediately.

### 3. Package globals

For symbols that should be in scope for every file in a consumer
project — type aliases, ambient constraints, shared kinds — without
each consumer file needing a `// ::types` directive. This is a config
key, not to be confused with the [`::global` directive](#global--extend-built-in-types)
(which registers methods/statics on types): `"globals"` makes a whole
declaration file ambient. Declare under the same `"hinmil"` block:

```json
{
  "hinmil": {
    "sidecars": "./sqlkit.hm",
    "globals": ["./sqlkit.hm"]
  }
}
```

`"globals"` **must be an array** (a bare string is rejected with a
warning). Every consumer file in the workspace automatically gets
these declarations merged into its environment.

### Merge order

When the same name appears in multiple sources, later wins:

```
bundled builtin  <  inline  <  sidecar  <  companion package  <  project-local override
```

A *bundled builtin* is a signature file shipped with the extension itself
([hm-types-builtin/](hm-types-builtin/)): `react` and `react-dom`, and the
Node modules `assert`, `buffer`, `child_process`, `crypto`, `fs`, `http`,
`os`, `path`, `url` and `zlib` (`node:fs` is the same as `fs`). It is the
weakest layer, and any package backed by one is *open-world*: importing a
name no layer declares binds it to `Any` instead of erroring, so an
outdated bundle can never be worse than no typings. A Node module without
a bundled file (for example `readline`) gives HM3003; add a project stub
in `hm-types/<module>.hm` (methods as `Type#method :: Type ~> …`).

A built-in type that has no `Name ::` declaration (such as `ReactElement`)
is documented in its bundled file with an anchor line `// ::builtin Name`;
go to definition on the type name jumps there.

A *companion package* is an `@hm/<pkg>` package that ships sidecars
for a package that has none itself (like `@types/*` in the TypeScript
world): `lodash` → `@hm/lodash`, `@scope/pkg` → `@hm/scope__pkg`. It
is only consulted when the package provides neither inline annotations
nor its own sidecar.

So a project can always shadow a published signature by declaring it
locally, a sidecar shadows inline annotations, and inline is the
fallback when nothing else is declared.

### Cross-package chaining

A `.js` or `.hm` source can pull in another package's types
explicitly with `// ::types`:

```javascript
// A bare specifier: recurse into that package's scan.
// ::types other-pkg

// A sibling JS file, and a sibling sidecar:
// ::types ./helper.js
// ::types ./types.hm
```

This is useful when your signatures reference types declared in a
dependency. Results are cached per package root, so transitive chains
don't re-scan on every import.

## Using a typed npm package (consumer side)

There is nothing to configure. Install and import:

```javascript
const { limit, add } = require('mylib');

const x = add(1)(2);     // hover shows: Number
const y = limit('hi');   // diagnostic: expected Number, got String
```

The LSP resolves `mylib` via Node's normal `node_modules` lookup,
applies sidecar (if any), falls back to inline scan, merges globals,
and caches the result per package root. Subsequent imports of the
same package are free.

The package's methods (`Type#method` in its sidecar or inline annotations)
come along with the import: `makeCart ().count ()` is typed as soon as
`makeCart` is imported. A `::types` directive is only needed for type-only
use — a file that names the package's types in its annotations but imports
nothing from it:

```javascript
// ::types sqlkit
// queryOf :: SqlKit -> String
const queryOf = (kit) => kit.toString ();
```

### When signatures don't show up

A few common gotchas:

- **No `main` / `module` in `package.json`** — the inline scan falls
  back to `index.{js,mjs,cjs}`. If that's also absent, no signatures.
- **Symlinked / linked package in dev (`npm link`, `pnpm`)** — usually
  works, but cache may go stale after edits inside `node_modules`.
  Restart the LSP if you're not seeing fresh signatures.
- **Annotation lives outside the package root** — the BFS won't follow
  `../` escapes. Use `// ::types <relative-or-bare>` to chain
  explicitly.
- **`"globals"` config key declared as a string** — ignored, with a
  warning. Always an array (see
  [Package globals](#3-package-globals)).
- **Re-export chain >256 files** — scan cap is hit; declare a sidecar
  for the affected names.

### Ramda

Ramda does not ship HM types itself.  The example project
[hinmil-example](https://github.com/tureluren/hinmil-example) has a
[`hm-types/ramda.hm`](https://github.com/tureluren/hinmil-example/blob/main/hm-types/ramda.hm)
for 84 of its most used functions (Ramda 0.29 and later), written with
[`::curried`](#curried--curried-library-functions).  Copy it to
`hm-types/ramda.hm` in your project, and named and namespace imports are
typed, in Ramda's curried style, with the `__` placeholder:

```javascript
import * as R from "ramda";

const orders = [
  { id: "o1", customer: "Ada", total: 120, paid: true },
  { id: "o2", customer: "Alan", total: 35, paid: false },
];

const unpaid = R.filter (R.propEq (false, "paid"), orders);  // the full order type
const byCustomer = R.groupBy (R.prop ("customer")) (orders);  // orders per customer: { [String] :: [{ id, customer, … }] }
const outstanding = R.pipe (R.map (R.prop ("total")), R.sum);  // [{ total :: Number, ...r }] -> Number
const withoutFee = R.subtract (R.__, 2.5);                     // Number -> Number

const broken = R.pipe (R.map (R.prop ("total")), R.sum, R.toUpper);
// ✗ Type mismatch: Cannot unify 'String' with 'Number'
```

A function that is not in the file is `Any` once Ramda is installed.

---

## Built-in Method Types

The LSP ships type definitions for the standard JavaScript built-ins: Array,
String, Object, Number, BigInt, RegExp, Promise, Map, Set, Math, Date
(including `Date.UTC` and the `setUTC…` setters), JSON, `Intl` formatters,
`URLSearchParams`, `AbortController`/`AbortSignal`, the timers
(`setTimeout`, … — their ids are `TimeoutId`/`IntervalId`) and, with
`hinmil.dom.globalTypes`, the browser DOM. `globalThis` is `Any`. Node
modules are typed through the bundled files listed under
[Merge order](#merge-order). The tables below show the most common methods —
hover any method call to see the exact signature.
Optional trailing parameters are written as `| Undefined`. A callback
result written `t` may be anything: `filter`, `find`, `some`, `every`,
`findIndex` and `findLast(Index)` read it as truthy/falsy, so
`orders.filter (o => o.paidAt)` needs no `Boolean`. `Awaited b` is `b`
with a returned promise unwrapped (`then (x => fetchNext (x))` gives
`Promise e Next`, not a promise of a promise).

### Array Methods

| Method | Type |
|--------|------|
| `map` | `((a, Number, [a]) -> b) -> [b]` |
| `filter` | `((a, Number, [a]) -> t) -> [a]` |
| `reduce` | `((b, a, Number, [a]) -> b, b \| Undefined) -> b` |
| `find` | `((a, Number, [a]) -> t) -> a` |
| `some` | `((a, Number, [a]) -> t) -> Boolean` |
| `every` | `((a, Number, [a]) -> t) -> Boolean` |
| `flatMap` | `((a, Number, [a]) -> [b]) -> [b]` |
| `forEach` | `((a, Number, [a]) -> b) -> ()` |
| `concat` | `[a] ~> ([b] \| b) -> [a \| b]` |
| `includes` | `(a, Number \| Undefined) -> Boolean` |
| `indexOf` | `(a, Number \| Undefined) -> Number` |
| `slice` | `(Number \| Undefined, Number \| Undefined) -> [a]` |
| `join` | `(String \| Undefined) -> String` |
| `reverse` | `[a]` |
| `toReversed` | `() -> [a]` |
| `toSorted` | `(((a, a) -> Number) \| Undefined) -> [a]` |
| `toSpliced` | `(Number \| Undefined, Number \| Undefined) -> [a]` (both arguments optional, with overloads for up to three items of type `a`) |
| `with` | `(Number, a) -> [a]` |
| `length` | `Number` (property) |
| ... | and more |

### String Methods

| Method | Type |
|--------|------|
| `charAt` | `(Number \| Undefined) -> String` |
| `includes` | `(String, Number \| Undefined) -> Boolean` |
| `indexOf` | `(String, Number \| Undefined) -> Number` |
| `split` | `(String \| RegExp \| Undefined, Number \| Undefined) -> [String]` |
| `slice` | `(Number \| Undefined, Number \| Undefined) -> String` |
| `startsWith` | `(String, Number \| Undefined) -> Boolean` |
| `replace` | `(RegExp \| String, String) -> String` |
| `padStart` | `(Number, String \| Undefined) -> String` |
| `toLowerCase` | `String` |
| `toUpperCase` | `String` |
| `trim` | `String` |
| `length` | `Number` (property) |
| ... | and more |

### Object Static Methods

| Method | Type |
|--------|------|
| `Object.keys` | `a -> [String]` |
| `Object.values` | `a -> [b]` |
| `Object.entries` | `a -> [[b]]` |
| `Object.fromEntries` | `[[b]] -> a` |
| `Object.assign` | `(a, b) -> { ...a, ...b }` (overloads for 1–4 arguments; dictionaries `Object k a` merge to `Object k (a ∪ b)`) |
| `Object.freeze` | `a -> a` |
| `Object.is` | `(a, a) -> Boolean` |
| `Object.hasOwn` | `(a, String) -> Boolean` |
| ... | and more |

These stay deliberately loose — objects flow through them without
forcing a specific record shape.

### Promise Methods

Promises are typed as `Promise e a` — error type first, value type second.

| Method | Type |
|--------|------|
| `then` | `(a -> b, (e -> c) \| Undefined) -> Promise e (Awaited b)` |
| `catch` | `(e -> b) -> Promise e b` |
| `finally` | `(() -> ()) -> Promise e a` |
| `Promise.resolve` | `a -> Promise e a` |
| `Promise.reject` | `e -> Promise e a` |
| `Promise.all` | `[Promise e a] -> Promise e [a]` |
| `Promise.race` | `[Promise e a] -> Promise e a` |
| `Promise.allSettled` | `[Promise e a] -> Promise e [a]` |
| `Promise.any` | `[Promise e a] -> Promise e a` |

### Map Methods

Typed as `Map k v`.

| Method | Type |
|--------|------|
| `get` | `k -> (v \| Undefined)` — see [lookups that can miss](#lookups-that-can-miss) |
| `set` | `(k, v) -> Map k v` |
| `has` | `k -> Boolean` |
| `delete` | `k -> Boolean` |
| `forEach` | `((v, k, Map k v) -> b) -> ()` |
| `keys` | `[k]` |
| `values` | `[v]` |
| `entries` | `[(k, v)]` |
| `size` | `Number` (property) |
| `Map.groupBy` | `([a], (a -> k)) -> Map k [a]` |

### Set Methods

Typed as `Set a`, including the newer set-operation methods.

| Method | Type |
|--------|------|
| `add` | `a -> Set a` |
| `has` | `a -> Boolean` |
| `delete` | `a -> Boolean` |
| `forEach` | `((a, a, Set a) -> b) -> ()` |
| `values` / `keys` | `[a]` |
| `entries` | `[(a, a)]` |
| `union` / `intersection` / `difference` / `symmetricDifference` | `Set a -> Set a` |
| `isSubsetOf` / `isSupersetOf` / `isDisjointFrom` | `Set a -> Boolean` |
| `size` | `Number` (property) |

---

## Configuration

HinMil reads settings from two places:

1. **Editor settings** — the `hinmil.*` namespace in VS Code (Settings UI or `settings.json`).
2. **Project file** — a `"settings"` key in the project config (`package.json#hinmil`, `hinmil.config.json` or `hinmil.config.js`). Project-file settings **override** editor settings, so a repository can pin its own diagnostics policy for every contributor.

Diagnostic categories share a uniform level enum — `off`, `hint`, `information`, `warning`, `error` — where `off` disables the category entirely.

### Configuration per folder (monorepos)

A file uses the **nearest** folder above it that has HinMil configuration
(`hinmil.config.json`, `hinmil.config.js` or a `"hinmil"` key in
`package.json`), up to the workspace root (or the CLI's `--project`).
Each such folder is its own *project scope* with its own `globals`,
`typesDir`, `overrides` and `settings`, so a `server/` and a `client/`
application can each declare their own `Order` type:

```text
shop/
├── hinmil.config.json          { }   ← workspace root (the editor needs one here)
├── server/
│   ├── hinmil.config.json      { "globals": ["./globals.hm"] }
│   ├── globals.hm             Order :: { id :: String, total :: Number }
│   └── src/orders.js          ← uses server/globals.hm
└── client/
    ├── hinmil.config.json      { "globals": ["./globals.hm"] }
    ├── globals.hm             Order :: { id :: String, lines :: [String] }
    └── src/summary.js         ← uses client/globals.hm
```

**Multi-root workspaces.** Every folder of a multi-root workspace is a
project of its own, with its own configuration, globals, file selection
(`files`) and project-file settings, and folders can be added or removed
while the editor runs. A folder with `"enable": false` in its
configuration is skipped: its files get no diagnostics, hover or other
answers. Settings that apply to the server as a whole (the diagnostics
debounce and the `dom` group) follow the first folder that is checked.

Within one workspace folder, the file selection (`files`) and the
project-file settings come from the editor and that folder's root
configuration; a configuration in a subfolder contributes its globals,
`typesDir` and `overrides`. Paths in a configuration (`globals`,
`typesDir`) are relative to its own folder. With `hinmil.requiresConfig`,
the language server starts only when a workspace folder itself has
configuration (an empty `{}` is enough), and only such folders are
checked.

### Enabling / disabling the language server

Once the extension is installed it activates for every JavaScript file. Two settings and one project-config key control whether the language server actually runs:

- **`hinmil.enable`** (editor setting, default `true`) — the master switch. Put `"hinmil.enable": false` in a project's `.vscode/settings.json` to turn HinMil off for that project while keeping it on everywhere else, or set it in your user settings to disable it globally.
- **`"enable": false`** (project config) — opt a repository out from within the repository itself, without touching editor settings. Works in `hinmil.config.json`, `hinmil.config.js`, and the `"hinmil"` key of `package.json`:

  ```jsonc
  // hinmil.config.json  (or  package.json → "hinmil": { "enable": false })
  { "enable": false }
  ```

- **`hinmil.requiresConfig`** (editor setting, default `false`) — opt-in mode. When `true`, the server only starts if at least one workspace folder has explicit HinMil project configuration **at its root**: a `hinmil.config.json` / `hinmil.config.js` file or a `"hinmil"` key in `package.json` (a configuration only in a subfolder does not count). In a multi-root workspace the folders without such configuration are then not checked. Set this once in your **user** settings and HinMil stays dormant in every project that hasn't opted in — no per-project settings needed.

All of these take effect immediately (no reload): toggling them starts or stops the server, and config-file changes are picked up the moment they happen. `hinmil.enable: false` wins over everything, including the restart command. Note that syntax highlighting of HM annotations is controlled separately by `hinmil.syntaxHighlighting.enabled`.

| Setting | Default | Description |
|---------|---------|-------------|
| `hinmil.enable` | `true` | Run the language server at all. Set to `false` in a workspace's `.vscode/settings.json` — or `"enable": false` in the project config file — to disable HinMil for one project only |
| `hinmil.requiresConfig` | `false` | Only start the language server when a workspace folder contains explicit HinMil project configuration (see below) |
| `hinmil.files.extensions` | `.js`, `.jsx`, `.mjs`, `.cjs`, `.hm` | Source extensions HinMil checks (see [Command-Line Checker](#command-line-checker)); also settable as `files` in the project config |
| `hinmil.files.include` | `**/*` | Globs of files to check |
| `hinmil.files.exclude` | `node_modules`, `.git`, `dist`, `build`, `coverage` | Globs of files not to check on their own (still inferred when imported). A list you set replaces the defaults |
| `hinmil.diagnostics.enabled` | `true` | Master switch for all diagnostics |
| `hinmil.diagnostics.typeErrors` | `error` | Level for type mismatch / unification errors (codes 1001–1004, 1009, 7001) |
| `hinmil.diagnostics.unknownPropertyAccess` | `error` | Level for property access on unknown or unconstrained types (codes 1005, 1006) |
| `hinmil.diagnostics.missingRecordFields` | `error` | Level for record values missing required fields (code 1008) |
| `hinmil.diagnostics.excessRecordFields` | `error` | Level for object-literal arguments with fields their named record type does not declare (code 1010) |
| `hinmil.diagnostics.annotationNarrowing` | `error` | Reserved: level for code 2009, which no check emits at the moment (an annotation narrower than the inferred union is reported as 1003, or allowed for a [lookup](#lookups-that-can-miss)). Kept so existing configurations stay valid |
| `hinmil.diagnostics.missingSignatures` | `information` | Level for functions without an HM annotation |
| `hinmil.diagnostics.missingVariableSignatures` | `off` | Level for variables without an HM annotation |
| `hinmil.diagnostics.trustAnnotations` | `off` | Trust user annotations and suppress diagnostics inside trusted bodies — see levels below |
| `hinmil.diagnostics.debounceMs` | `500` | Delay (ms) before publishing diagnostics after an edit. Only affects diagnostics — hover, completion and signature help respond immediately |
| `hinmil.display.typeVariables` | `pretty` | Type-variable display: `pretty` (a, b, c) or `raw` (internal names) |
| `hinmil.hover.enabled` | `true` | Show inferred types on hover |
| `hinmil.completion.enabled` | `true` | Enable autocompletion |
| `hinmil.completion.autoImports` | `true` | Suggest exports from other workspace files with an automatic import edit |
| `hinmil.signatureHelp.enabled` | `true` | Show parameter info on function calls |
| `hinmil.navigation.definitions` | `auto` | Go to definition for module paths, imported names and local names (see [Go to definition](#go-to-definition)): `auto` (only when VS Code's built-in TypeScript/JavaScript extension is not active), `always`, `off` |
| `hinmil.dom.globalTypes` | `true` | Typed browser globals (`document` → `Document`, …) with IntelliSense on the compact DOM catalogue; DOM type names become valid in annotations. Off reverts the globals to `Any` |
| `hinmil.dom.strictNulls` | `false` | DOM lookups that can miss (`getElementById`, `querySelector`, `getAttribute`, `getItem`, …) return `T \| Null` |
| `hinmil.syntaxHighlighting.enabled` | `true` | Highlight HM annotations in comments (requires reload) |
| `hinmil.trace.server` | `off` | LSP message tracing between VS Code and the server (`off`, `messages`, `verbose`) |

### Project-file settings

The project config has these top-level keys: `enable` (opt the project out, see above), `globals`, `overrides`, `typesDir`, `files` (the file selection, see [Command-Line Checker](#command-line-checker)) and `settings`. Inside `settings` go the setting groups of the table above — `diagnostics`, `display`, `hover`, `completion`, `signatureHelp`, `navigation`, `dom` — without the `hinmil.` prefix. `requiresConfig`, `syntaxHighlighting` and `trace` are editor-only. Project-file settings win over editor settings and are hot-reloaded when the file changes:

```jsonc
// package.json
{
  "hinmil": {
    "globals": ["./globals.hm"],
    "settings": {
      "diagnostics": { "typeErrors": "warning", "missingSignatures": "off" },
      "display": { "typeVariables": "raw" }
    }
  }
}
```

The same `"settings"` key works in a standalone `hinmil.config.json` or `hinmil.config.js` (`module.exports = { settings: { … } }`).

#### `trustAnnotations` levels

Cumulative tiers — each level includes everything the previous one does.
`missingSignatures` / `missingVariableSignatures` are **orthogonal** and remain
active on every level.

| Level | Behaviour |
|-------|-----------|
| `"off"` *(default)* | Full validation. Annotation-vs-inferred mismatches and every in-body type error are reported. |
| `"signatures"` | Trust signatures: drop annotation mismatches (code 1003) so a `::` annotation is treated as ground truth, but body type errors are still surfaced. |
| `"annotated-bodies"` | Above, plus suppress every diagnostic whose range falls **inside a binding that carries a `::` annotation**. Use when annotated bodies are considered "audited" and you only want errors in unannotated code. |
| `"all-bodies"` | Above, plus suppress diagnostics inside **every** top-level binding (annotated or not). Only diagnostics outside binding bodies (e.g. top-level expression statements, missing-signature notices) remain. |

Any unrecognized value falls back to `"off"` with a warning.

---

## Command-Line Checker

Install the npm CLI as a development dependency and run the same project-aware checker outside the editor:

```bash
npm install --save-dev hinmil
npx hinmil .
```

```text
hinmil [paths...] [options]

--project <directory>   Project root (default: current directory)
--config <file>         Explicit hinmil JSON or JS config
--format stylish|json   Human-readable or machine-readable output
--ext <extension>       Add an extension (repeatable; e.g. --ext .vue)
--help, -h              Show usage
--version, -v           Show the package version
```

With no paths the project root is scanned. File selection is loaded **before** discovery. The built-in extensions are `.js`, `.jsx`, `.mjs`, `.cjs`, and `.hm`; `--ext` adds to (rather than replaces) the effective list. Explicit file and directory arguments obey the same extension/include/exclude filters as discovered files.

Configure selection in `package.json#hinmil`, `hinmil.config.json`, or `hinmil.config.js`:

```json
{
  "files": {
    "extensions": [".js", ".jsx", ".mjs", ".cjs", ".hm", ".custom"],
    "include": ["src/**", "types/**"],
    "exclude": ["**/*.generated.js", "**/vendor/**"]
  }
}
```

The precedence is built-in defaults → VS Code `hinmil.files.*` → project `files`; each specified array replaces the lower layer. So an `exclude` of your own must repeat the defaults you still want (`**/node_modules/**`, `**/.git/**`, `**/dist/**`, `**/build/**`, `**/coverage/**`). CLI `--ext` additions apply last. An explicitly empty `include` array selects no files. Exclusion suppresses only standalone diagnostics: an excluded module imported by a selected file is still parsed and inferred. Discovery visits each real directory once and follows symlinked directories only when they stay inside the project root.

For custom source extensions in VS Code, map them to JavaScript so the editor sends the document with the right language id:

```json
{
  "files.associations": { "*.custom": "javascript" },
  "hinmil.files.extensions": [".js", ".jsx", ".mjs", ".cjs", ".hm", ".custom"]
}
```

Without `--config`, each file is checked with the configuration of its nearest folder (see [Configuration per folder](#configuration-per-folder-monorepos)); within one folder, discovery uses `package.json#hinmil`, then `hinmil.config.js`, then `hinmil.config.json`. An explicit `--config` applies to every file. The file selection (`files`) always comes from the project root (or `--config`). JavaScript config is limited to a JSON-compatible `module.exports` object and is not executed. Exit status is `0` without error diagnostics, `1` with errors, and `2` for argument/config/input failures.

Use `--format json` for machine-readable output. It emits one object containing `project`, the ordered `checkedFiles`, configuration `warnings`, and ordered `diagnostics`; each diagnostic contains its absolute `file`, severity, HM code, message, and zero-based LSP `range`. A typical CI script can rely directly on the exit status:

```json
{
  "scripts": {
    "typecheck:hm": "hinmil --format json"
  }
}
```

```bash
npm run typecheck:hm
```

---

## Diagnostic Codes Reference

| Code | Category | Description |
|------|----------|-------------|
| **1001** | Type Error | Type mismatch — cannot unify types |
| **1002** | Type Error | Infinite type detected |
| **1003** | Type Error | Annotation mismatch |
| **1004** | Type Error | Return type doesn't match annotation |
| **1005** | Type Error | Missing property on record |
| **1006** | Type Error | Unconstrained property access on type variable |
| **1007** | Type Error | Unbound variable |
| **1008** | Type Error | Record value missing required fields |
| **1009** | Type Error | Value is not callable |
| **1010** | Type Error | Object literal has a field its named record type (alias) does not declare — usually a typo in an optional field (`form` for `from :: Date \| Undefined`); comes with a "did you mean" hint |
| **2001** | Annotation | Invalid annotation syntax |
| **2002** | Annotation | Declaration name doesn't match annotation name |
| **2003** | Annotation | Method name mismatch |
| **2004** | Annotation | Unknown type constructor |
| **2005** | Annotation | Using variant method instead of parent method |
| **2006** | Annotation | Method type mismatch |
| **2007** | Annotation | Nameless annotation (`:: Type`) placed on a named declaration |
| **2008** | Annotation | Type constructor applied to the wrong number of arguments |
| **2009** | Annotation | Reserved (not emitted at the moment; see `annotationNarrowing`) |
| **2010** | Annotation | Missing runtime argument for a `TypeRep` parameter |
| **2011** | Annotation | Bare type variable used as a value annotation |
| **2012** | Annotation | Method annotation on a bare value type |
| **2013** | Annotation | Instance-callable annotation (`Type() ::`) on a type with no constructor |
| **2014** | Annotation | Method or static annotation on a type with no constructor |
| **2015** | Annotation | Invalid `::narrow` directive |
| **3001** | Module | Missing export |
| **3002** | Module | Unresolved `::types` path |
| **3003** | Module | Unresolved import |
| **3004** | Module | Duplicate import |
| **3005** | Module | Circular import |
| **4001** | Constraint | Unknown constraint name |
| **4002** | Constraint | Constraint violation |
| **4003** | Constraint | Invalid constraint definition |
| **4004** | Constraint | Constraint kind mismatch (e.g. concrete type where a container is required) |
| **5001** | Curry | Curry arity mismatch |
| **5002** | Curry | Curry type error, or `::curried` in a JavaScript file (only `.hm` files) |
| **5003** | Curry | Over-application of curried function |
| **5004** | Curry | Fan-out arity mismatch |
| **6001** | Info | Missing annotation (informational). Not reported for a point-free binding (`const total = pipe (map (prop ("total")), sum)`); a call that wraps one function literal (`curry ((a, b) => …)`) is still asked |
| **6002** | Info | Sum type variant missing an annotated method implementation |
| **7001** | Relation | Invalid table relation / picked projection |
| **9001** | Parse | Source code parse error |

---

## Example: Full Workflow

A small module that combines annotations, a sum type, a constraint, and
narrowing:

```javascript
// Maybe :: Just a | Nothing

class Just {
  // Just :: a -> Maybe a
  constructor(value) { this.value = value; }
  // Maybe#map :: Maybe a ~> (a -> b) -> Maybe b
  map(fn) { return new Just(fn(this.value)); }
}

// Nothing :: Maybe a
class Nothing {
  map(_fn) { return new Nothing(); }
}

// ::constraint Functor f { f :: { map :: f a ~> (a -> b) -> f b } }

// fmap :: Functor f => ((a -> b), f a) -> f b
const fmap = (fn, f) => f.map(fn);

// findDiscount :: Number -> Maybe Number
const findDiscount = (total) =>
  total < 500 ? new Nothing() : new Just(total * 0.05);

// discounts :: [Number] -> [Maybe Number]
const discounts = (totals) => totals.map(findDiscount);

// ::narrow Number
// isNumber :: a -> Boolean
const isNumber = (x) => typeof x === 'number';

// formatReference :: (Number | String) -> String
const formatReference = (x) => {
  if (isNumber(x)) {
    return x.toFixed(0);  // x: Number (narrowed)
  }
  return x;               // x: String (narrowed)
};
```

---

## License

MIT — see [LICENSE](LICENSE).
