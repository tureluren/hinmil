// ============================================================================
// Isolated tarball test (opt-in: `npm run test:tarball`).
//
// Proves the published npm package is self-contained: packs `npm/cli` (which
// runs the real prepack build), extracts the tarball into a temp directory,
// and runs the CLI from the extracted package against a fresh temp project —
// so no repository file can be used accidentally. Declared dependencies are
// resolved through NODE_PATH to the repository's node_modules, keeping the
// test offline; a full `npm install <tarball>` check needs network access.
// ============================================================================

import { execFileSync, spawnSync } from 'child_process';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';

const repoRoot = path.resolve(__dirname, '..');

function fail(message: string): never {
  console.error(`tarball-test: FAIL — ${message}`);
  process.exit(1);
}

function assert(condition: boolean, message: string): void {
  if (!condition) fail(message);
}

const work = fs.mkdtempSync(path.join(os.tmpdir(), 'hinmil-tarball-'));
try {
  // 1. Pack the npm package (runs prepack → full build + copy).
  console.log('packing npm/cli …');
  const packOutput = execFileSync(
    'npm', ['pack', './npm/cli', '--pack-destination', work],
    { cwd: repoRoot, encoding: 'utf8' },
  ).trim();
  const tarball = path.join(work, packOutput.split('\n').pop()!.trim());
  assert(fs.existsSync(tarball), `npm pack did not produce ${tarball}`);

  // 2. The tarball must not leak repository-only files.
  const listing = execFileSync('tar', ['-tzf', tarball], { encoding: 'utf8' });
  assert(listing.includes('package/dist/cli.js'), 'dist/cli.js missing from tarball');
  assert(listing.includes('package/dist/services/projectChecker.js'), 'projectChecker.js missing from tarball');
  assert(listing.includes('package/LICENSE'), 'LICENSE missing from tarball');
  assert(listing.includes('package/dist/server.js'), 'dist/server.js (hinmil-lsp) missing from tarball');
  assert(!listing.includes('package/dist/extension.js'), 'extension client leaked into tarball');
  assert(!/package\/(src|tests|sample|scripts|coverage)\//.test(listing), 'repository sources leaked into tarball');

  // 3. Extract and build an isolated consumer project.
  execFileSync('tar', ['-xzf', tarball, '-C', work]);
  const packageDir = path.join(work, 'package');
  const project = path.join(work, 'project');
  fs.mkdirSync(project);
  fs.writeFileSync(path.join(project, 'hinmil.config.json'), JSON.stringify({
    settings: { diagnostics: { missingSignatures: 'off' } },
  }));
  fs.writeFileSync(path.join(project, 'ok.js'), '// value :: Number\nconst value = 1;\n');
  fs.writeFileSync(path.join(project, 'bad.js'), '// broken :: Number\nconst broken = "nope";\n');

  // 4. Run the CLI from the extracted package only.
  const env = { ...process.env, NODE_PATH: path.join(repoRoot, 'node_modules') };
  const run = (args: string[]): { stdout: string; code: number } => {
    try {
      const stdout = execFileSync(
        'node', [path.join(packageDir, 'dist', 'cli.js'), ...args],
        { cwd: project, encoding: 'utf8', env },
      );
      return { stdout, code: 0 };
    } catch (error) {
      const failure = error as { stdout?: string; status?: number };
      return { stdout: String(failure.stdout ?? ''), code: failure.status ?? -1 };
    }
  };

  const version = run(['--version']);
  assert(version.code === 0, `--version exited ${version.code}`);
  assert(/^\d+\.\d+\.\d+/.test(version.stdout.trim()), `--version printed ${JSON.stringify(version.stdout.trim())}`);

  const check = run(['--format', 'json']);
  assert(check.code === 1, `expected exit 1 for a project with one error, got ${check.code}`);
  const output = JSON.parse(check.stdout) as {
    checkedFiles: string[];
    diagnostics: Array<{ file: string; severity: string }>;
  };
  assert(output.checkedFiles.length === 2, `expected 2 checked files, got ${output.checkedFiles.length}`);
  const errors = output.diagnostics.filter((diagnostic) => diagnostic.severity === 'error');
  assert(errors.length === 1 && errors[0].file.endsWith('bad.js'),
    `expected exactly one error in bad.js, got ${JSON.stringify(output.diagnostics)}`);

  // 5. The language server: `hinmil-lsp` is a bin with a shebang, and it
  //    answers `initialize` over stdio from the extracted package.
  const manifest = JSON.parse(fs.readFileSync(path.join(packageDir, 'package.json'), 'utf8')) as { bin: Record<string, string> };
  assert(manifest.bin['hinmil-lsp'] === 'dist/server.js', `bin hinmil-lsp is ${JSON.stringify(manifest.bin['hinmil-lsp'])}`);
  assert(fs.readFileSync(path.join(packageDir, 'dist', 'server.js'), 'utf8').startsWith('#!/usr/bin/env node'),
    'dist/server.js has no shebang');
  const lsp = spawnSync('node', ['-e', `
    const { spawn } = require ('child_process');
    const p = spawn ('node', [${JSON.stringify(path.join(packageDir, 'dist', 'server.js'))}, '--stdio'], { cwd: ${JSON.stringify(project)} });
    const body = JSON.stringify ({ jsonrpc: '2.0', id: 1, method: 'initialize', params: { processId: null, rootUri: null, capabilities: {} } });
    let out = '';
    p.stdout.on ('data', (d) => { out += d; if (out.includes ('"capabilities"')) { console.log (out.includes ('"hoverProvider":true') ? 'ok' : 'no hover'); p.kill (); process.exit (0); } });
    p.stdin.write ('Content-Length: ' + Buffer.byteLength (body) + '\\r\\n\\r\\n' + body);
    setTimeout (() => { console.log ('timeout'); p.kill (); }, 15000);
  `], { cwd: project, encoding: 'utf8', env });
  assert(lsp.stdout.trim().split('\n').pop() === 'ok', `hinmil-lsp did not answer initialize: ${JSON.stringify(lsp.stdout + lsp.stderr)}`);

  console.log(`tarball-test: PASS (${path.basename(tarball)}, version ${version.stdout.trim()}, hinmil-lsp ok)`);
} finally {
  fs.rmSync(work, { recursive: true, force: true });
}
