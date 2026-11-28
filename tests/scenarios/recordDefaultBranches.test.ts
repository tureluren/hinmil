// A conditional that picks a default record or a typed one, as in a job
// scheduler that reads optional per-queue settings:
//
//   const retry = queue.retry == null ? { attempts: undefined, delayMs: undefined } : queue.retry;
//
// With `queue.retry :: { attempts :: Number | Undefined, … } | Null` the
// result is the wider record (`attempts :: Number | Undefined`), not the
// literal's `{ attempts :: Undefined }`; so `retry.attempts == null ? 3 :
// retry.attempts` is `Number`.  Before, the literal branch won and the
// Number was lost.

import * as fs from 'fs';
import * as path from 'path';
import { runCli } from '../../src/cli';

const ROOT = '/tmp/hm-scenarios-record-default-branches';

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
  fs.writeFileSync(path.join(ROOT, 'package.json'), '{ "name": "record-default-branches" }');
});

const TYPES = `// Retry :: { attempts :: Number | Undefined, delayMs :: Number | Null | Undefined, codes :: [Number] | Undefined }
// Queue :: { name :: String, retry :: Retry | Null }
// Policy :: { queue :: String, attempts :: Number, delayMs :: Number | Null, codes :: [Number] }
`;

test('positive: a literal default and a typed record give the wider record', () => {
  expect(lint('literalDefault', `${TYPES}
// policyOf :: Queue -> Policy
export const policyOf = queue => {
  const retry = queue.retry == null ? { attempts: undefined, delayMs: undefined, codes: undefined } : queue.retry;
  return {
    queue: queue.name,
    attempts: retry.attempts == null ? 3 : retry.attempts,
    delayMs: retry.delayMs == null ? null : retry.delayMs,
    codes: retry.codes == null ? [502, 503] : retry.codes
  };
};

// delayOf :: Queue -> Number | Null
export const delayOf = queue => {
  const retry = queue.retry == null ? { attempts: undefined, delayMs: undefined, codes: undefined } : queue.retry;
  return retry.delayMs == null ? null : retry.delayMs;
};
`)).toEqual([]);
});

test('positive: the typed record first, and a named default, behave the same', () => {
  expect(lint('typedFirst', `${TYPES}
// NO_RETRY :: Retry
const NO_RETRY = { attempts: undefined, delayMs: undefined, codes: undefined };

// attemptsOf :: Queue -> Number
export const attemptsOf = queue => {
  const retry = queue.retry != null ? queue.retry : { attempts: undefined, delayMs: undefined, codes: undefined };
  return retry.attempts == null ? 3 : retry.attempts;
};

// namedAttempts :: Queue -> Number
export const namedAttempts = queue => {
  const retry = queue.retry == null ? NO_RETRY : queue.retry;
  return retry.attempts == null ? 3 : retry.attempts;
};
`)).toEqual([]);
});

test('positive: nested records widen field by field', () => {
  expect(lint('nested', `// Backoff :: { baseMs :: Number | Undefined }
// Limits :: { backoff :: Backoff, label :: String }
// Worker :: { limits :: Limits | Null }

// baseOf :: Worker -> Number
export const baseOf = worker => {
  const limits = worker.limits == null ? { backoff: { baseMs: undefined }, label: "default" } : worker.limits;
  const backoff = limits.backoff;
  return backoff.baseMs == null ? 1000 : backoff.baseMs;
};
`)).toEqual([]);
});

test('negative: the widened field is still optional without a null check', () => {
  const errors = lint('noCheck', `${TYPES}
// attemptsOf :: Queue -> Number
export const attemptsOf = queue => {
  const retry = queue.retry == null ? { attempts: undefined, delayMs: undefined, codes: undefined } : queue.retry;
  return retry.attempts;
};
`);
  expect(errors.length).toBe(1);
  expect(errors[0]).toMatch(/attemptsOf/);
});

test('negative: a filled-in default does not hide the optional field of the typed branch', () => {
  // The literal says Number, the typed branch Number | Undefined: the
  // result is optional, so returning it as Number is an error (before, the
  // literal branch won and this passed).
  const errors = lint('filledDefault', `${TYPES}
// attemptsOf :: Queue -> Number
export const attemptsOf = queue => {
  const retry = queue.retry == null ? { attempts: 3, delayMs: null, codes: [] } : queue.retry;
  return retry.attempts;
};
`);
  expect(errors.length).toBe(1);
  expect(errors[0]).toMatch(/attemptsOf/);
});
