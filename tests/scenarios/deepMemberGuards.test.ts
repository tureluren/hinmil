// Null checks on a nested field, as in a worker that reads optional limits
// from its settings record:
//
//   settings.limits.backoffMs == null ? 1000 : settings.limits.backoffMs
//
// The check narrows the field at that path (every record on the way is
// rebuilt), in a ternary, after an early-return guard and on the right of
// `&&`.  Before, only `ident.prop` narrowed; a deeper path kept
// `Number | Undefined`.

import * as fs from 'fs';
import * as path from 'path';
import { runCli } from '../../src/cli';

const ROOT = '/tmp/hm-scenarios-deep-member-guards';

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
  fs.writeFileSync(path.join(ROOT, 'package.json'), '{ "name": "deep-member-guards" }');
});

const TYPES = `// Limits :: { backoffMs :: Number | Undefined, label :: String | Null }
// Retry :: { limits :: Limits, attempts :: Number }
// Settings :: { name :: String, retry :: Retry }
`;

test('positive: a ternary on a nested field narrows that field', () => {
  expect(lint('ternary', `${TYPES}
// backoffOf :: Settings -> Number
export const backoffOf = settings =>
  settings.retry.limits.backoffMs == null ? 1000 : settings.retry.limits.backoffMs;

// labelOf :: Settings -> String
export const labelOf = settings =>
  settings.retry.limits["label"] !== null ? settings.retry.limits["label"] : settings.name;
`)).toEqual([]);
});

test('positive: an early return and the right of && narrow the nested field', () => {
  expect(lint('guards', `${TYPES}
// delayOf :: Settings -> Number -> Number
export const delayOf = settings => attempt => {
  if (settings.retry.limits.backoffMs == null) return 0;
  return settings.retry.limits.backoffMs * 2 ** attempt;
};

// longBackoff :: Settings -> Boolean
export const longBackoff = settings =>
  settings.retry.limits.backoffMs != null && settings.retry.limits.backoffMs > 60000;
`)).toEqual([]);
});

test('negative: the branch where the nested field is missing stays optional', () => {
  const errors = lint('wrongBranch', `${TYPES}
// backoffOf :: Settings -> Number
export const backoffOf = settings =>
  settings.retry.limits.backoffMs != null ? 1000 : settings.retry.limits.backoffMs;
`);
  expect(errors.length).toBe(1);
  expect(errors[0]).toMatch(/backoffOf/);
});

test('negative: checking one nested field does not narrow its sibling', () => {
  const errors = lint('sibling', `${TYPES}
// labelOf :: Settings -> String
export const labelOf = settings =>
  settings.retry.limits.backoffMs == null ? "none" : settings.retry.limits.label;
`);
  expect(errors.length).toBe(1);
  expect(errors[0]).toMatch(/labelOf/);
});
