// Node.js core modules through the bundled stubs in `hm-types-builtin/`
// (path, url, assert, fs, child_process) — named, namespace, default and `node:` imports.
// Patterns from the app's server (`src/config/env.js`, the smoke tests) and
// typical server scripts.  Previously each project needed its own
// `hm-types/<builtin>.hm` or got HM3003 "Cannot resolve module".

import * as fs from 'fs';
import * as path from 'path';
import { runCli } from '../../src/cli';

const ROOT = '/tmp/hm-scenarios-node-builtins';

function lint(name: string, source: string): string[] {
  fs.mkdirSync(path.join(ROOT, 'src'), { recursive: true });
  fs.writeFileSync(path.join(ROOT, 'src', `${name}.js`), source);
  let stdout = '';
  runCli([`src/${name}.js`, '--project', '.'], {
    cwd: ROOT,
    stdout: (t) => { stdout += t; },
    stderr: () => {},
  });
  return stdout.split('\n').filter((l) => / error /.test(l));
}

beforeAll(() => {
  fs.rmSync(ROOT, { recursive: true, force: true });
  fs.mkdirSync(ROOT, { recursive: true });
  fs.writeFileSync(path.join(ROOT, 'package.json'), '{ "name": "builtins-scenario" }');
});

test('positive: every import form resolves to typed signatures', () => {
  expect(lint('config', `import { join, dirname } from "path";
import * as fs from "node:fs";
import path from "path";
import { fileURLToPath } from "node:url";
import { ok, strictEqual } from "assert";

// configPath :: String -> String
export const configPath = root => join (root, "config", "env.json");
// here :: String
export const here = dirname (fileURLToPath ("file:///srv/app/server/src/config/env.js"));
// readConfig :: String -> String
export const readConfig = p => fs.existsSync (p) ? fs.readFileSync (p, "utf-8") : "";
// abs :: String -> String
export const abs = p => path.resolve (p);
// checkCount :: Number -> ()
export const checkCount = n => { ok (n > 0, "positive"); strictEqual (n, 3, "verwacht 3"); };
`)).toEqual([]);
});

test('negative: a Number passed to path.join', () => {
  expect(lint('join', `import { join } from "path";

// seasonDir :: Number -> String
export const seasonDir = year => join ("data", year);
`)).toEqual([
    "src/join.js:4:48 error HM1001 Type mismatch: Cannot unify 'Number' with 'String'",
  ]);
});

test('negative: an overloaded builtin whose RESULT conflicts names the result, not the arguments', () => {
  expect(lint('read', `import * as fs from "fs";

// readCount :: String -> Number
export const readCount = p => fs.readFileSync (p, "utf-8");
`)).toEqual([
    "src/read.js:4:31 error HM1001 Type mismatch: Cannot unify 'String' with 'Number'",
  ]);
});

test('buffer: require ("buffer") exposes the Buffer statics', () => {
  expect(lint('bytes', `const { Buffer } = require ("buffer");

// bytes :: String -> Buffer
const bytes = s => Buffer.from (s);
// size :: String -> Number
const size = s => Buffer.byteLength (s);

module.exports = { bytes, size };
`)).toEqual([]);
});

test('child_process and process.stdout: a script that runs a CLI and reports', () => {
  expect(lint('runner', `import { spawnSync } from "child_process";

// countLines :: [String] -> Number
export const countLines = args => {
  const p = spawnSync (process.execPath, args, { encoding: "utf8" });
  process.stdout.write (\`exit \${p.status}\\n\`);
  return \`\${p.stdout}\`.split ("\\n").length;
};
`)).toEqual([]);
});

test('negative: process.stdout.write takes a String', () => {
  expect(lint('write', `// report :: Number -> Boolean
export const report = n => process.stdout.write (n);
`)).toEqual([
    "src/write.js:2:50 error HM1001 Type mismatch: Cannot unify 'Number' with 'String'",
  ]);
});

test('fetch with a timeout signal: AbortSignal.timeout', () => {
  expect(lint('fetchJson', `// getStatus :: String -> Promise Error Number
export const getStatus = url =>
  fetch (url, { signal: AbortSignal.timeout (5000) }).then (res => res.status);

// signal :: AbortSignal
export const signal = AbortSignal.any ([AbortSignal.timeout (100), AbortSignal.abort ()]);
`)).toEqual([]);
});

test('negative: AbortSignal.timeout takes milliseconds as a Number', () => {
  expect(lint('badTimeout', `// signalFor :: String -> AbortSignal
export const signalFor = s => AbortSignal.timeout (s);
`)).toEqual([
    "src/badTimeout.js:2:52 error HM1001 Type mismatch: Cannot unify 'String' with 'Number'",
  ]);
});

test('URLSearchParams: build a query string from a record', () => {
  expect(lint('query', `// queryOf :: { page :: Number, q :: String } -> String
export const queryOf = p => new URLSearchParams ({ page: String (p.page), q: p.q }).toString ();

// pageOf :: String -> String | Null
export const pageOf = query => new URLSearchParams (query).get ("page");
`)).toEqual([]);
});

test('negative: URLSearchParams#get may miss', () => {
  expect(lint('queryBad', `// pageOf :: String -> String
export const pageOf = query => new URLSearchParams (query).get ("page");
`)).toEqual([
    "src/queryBad.js:2:14 error HM1003 Type mismatch: 'pageOf' has type 'String -> Null | String' but annotation expects 'String -> String'",
  ]);
});

test('zlib: compress and decompress text', () => {
  expect(lint('gzip', `import { gunzipSync, gzipSync } from "zlib";

// roundTrip :: String -> String
export const roundTrip = text => gunzipSync (gzipSync (text)).toString ("utf8");
`)).toEqual([]);
});

test('negative: gunzipSync takes a Buffer, not a String', () => {
  expect(lint('gunzipBad', `import { gunzipSync } from "zlib";

// unpack :: String -> Buffer
export const unpack = text => gunzipSync (text);
`)).toEqual([
    "src/gunzipBad.js:4:43 error HM1001 Type mismatch: Cannot unify 'String' with 'Buffer'",
  ]);
});


test('readline: default import creates an interface and reads input', () => {
  expect(lint('readline', `import readline from "readline";

const rl = readline.createInterface({ input: process.stdin, output: process.stdout });
rl.on("line", (line) => console.log(line));
rl.question("Your name: ", (answer) => console.log(answer));
rl.close();
`)).toEqual([]);
});

test('negative: readline question callback requires a String prompt', () => {
  expect(lint('readlineBad', `import { createInterface } from "readline";

const rl = createInterface({ input: process.stdin, output: process.stdout });
rl.question(123, (answer) => console.log(answer));
`)).toEqual([
  "src/readlineBad.js:4:13 error HM1001 Type mismatch: Cannot unify 'Number' with 'String'",
]);
});
