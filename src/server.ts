// ============================================================================
// LSP Server — Language Server Protocol entry point
//
// Plain language: the switchboard between the editor and the type checker.
// VS Code sends requests over the Language Server Protocol ("the user is
// hovering here", "the file changed", "give completions") and this file
// routes each request to the right service in src/services/, manages the
// per-document caches, and sends the answers back.  NOTE: this file has no
// direct test coverage — be extra careful when changing it.
// ============================================================================

import {
  createConnection,
  TextDocuments,
  ProposedFeatures,
  InitializeParams,
  InitializeResult,
  TextDocumentSyncKind,
  Hover,
  HoverParams,
  CompletionItem,
  CompletionParams,
  CompletionTriggerKind,
  SignatureHelp,
  SignatureHelpParams,
  DefinitionParams,
  Location,
  LocationLink,
  DidChangeWatchedFilesParams,
  DidChangeConfigurationNotification,
  DidChangeWatchedFilesNotification,
  Disposable,
  CodeActionParams,
  CodeAction,
  CodeActionKind,
  DocumentSymbolParams,
  DocumentSymbol,
  ReferenceParams,
  RenameParams,
  PrepareRenameParams,
  WorkspaceEdit,
  Range,
  Diagnostic,
  DiagnosticSeverity,
} from 'vscode-languageserver/node';

import * as path from 'path';
import * as fs from 'fs';
import { fileURLToPath, pathToFileURL } from 'url';
import { TextDocument } from 'vscode-languageserver-textdocument';
import { InferenceEngine, InferenceResult, ImportResolver, TypeDirectiveResolver, ImportTypeAliasResolver, extractTypeDirectivesWithLocations } from './index';
import { snapshotBuiltinOriginalEntries, restoreBuiltinOriginalEntries, snapshotMethodRegistry, MethodRegistrySnapshot, applyDomSettings } from './registries/methodRegistry';
import { extractImportModuleSpecifiers } from './commentParser';
import { scrubSkolems } from './hm/typeUtils';
import { buildHover, getAliasHoverAtOffset, validIdentLooksLikeArrayMethod, tryArrayLiteralReinfer, getWordAt, isOffsetInAnyAnnotation, isOffsetInComment, getNarrowDirectiveTypeAtOffset, isOffsetInConstraintDirective, reflowHover, buildScopeSeedType, applyDeclaredSchemeDisplay } from './services/hover';
import { configureModuleExtensions, resolveImportSpecifier, resolveTypeDirectiveSpecifier, extractImportSpecifiers, normalizeArrayLiteralASI, mapOffset, unmapOffset, patchArrayLiteralASI, findTypeDefinitionLocation, positionAt, clearHmSidecarCache, clearInlinePackageCache, clearInlinePackageCacheForPackage, evictHmSidecar, findPackageJson } from './services/files';
import { getDestructuringCompletions, getImportSpecifierCompletions, getImportPathCompletions, getTypeDirectivePathCompletions, getIdentifierCompletions, getDotCompletions, getBracketStringCompletions, getTableSelectorCompletions, getSumTypeRecordCompletions, getTypeAliasRecordCompletions, getAnnotationTypeCompletions, getAnnotationNameCompletions, getDirectiveCompletions, getJSXPropCompletions, getJSXComponentCompletions, getJSXStyleKeyCompletions, warmWorkspaceExports, invalidateWorkspaceExportEntry, CompletionContext } from './services/completion';
import { getCodeActions, CodeActionContext } from './services/codeActions';
import { getDocumentSymbols, DocumentSymbolContext } from './services/documentSymbols';
import { collectReferences } from './services/references';
import { findCodeDefinition, CodeDefinition } from './services/definitions';
import { ImportInferenceContext } from './services/importContext';
import { provideSignatureHelp } from './services/signatureHelp';
import { canShortCircuit } from './services/shortCircuit';
import { provideReferences, providePrepareRename, provideRename } from './services/rename';
import { clearFsProbeCache } from './services/fsProbe';
import { getHmDiagnostics, getHmHover, getHmDefinition, getHmDocumentSymbols, clearHmParseCacheForFile, HmServiceContext } from './services/hmFileServices';
import { loadProjectConfig, loadGlobalsFile, GlobalsLoaderDeps } from './services/globalsLoader';
import { cachedResults, lastValidatedSource, validatedUnderGeneration, lastPublishedDiagnostics, lastImportSpecifiers, lastSeenSource, lastEditPosition, WORD_BOUNDARY_GATE_MS, isIdentChar, computeCaretOffset, requestInferCache, REQUEST_INFER_SLOTS } from './services/documentCache';
import { buildDiagnostics } from './services/projectChecker';
import { mergeFileSelection } from './services/fileSelection';
import { SelectionRoot, isFileChecked, planFileSelectionRefresh, rootForFile } from './services/fileSelectionRefresh';

// ---------------------------------------------------------------------------
// Create a connection & document manager
// ---------------------------------------------------------------------------

const connection = createConnection(ProposedFeatures.all);
const documents = new TextDocuments(TextDocument);

import { HinMilSettings, HinMilProjectConfig, defaultSettings, mergeSettings, DEFAULT_GLOBALS_FILES, DEFAULT_TYPES_DIR, findScopeRoot, hasProjectConfig } from './config';
import { debugLog } from './debugLog';

/**
 * Debounce (ms) used for re-validating consumer documents after a `.hm`
 * sidecar change.  Much shorter than the keystroke debounce: the user
 * already committed an intent (save), so further coalescing buys little
 * and just adds visible latency before diagnostics refresh in dependent
 * files.  Keystroke-driven `.js` edits keep using `diagnostics.debounceMs`.
 */
const HM_REVALIDATE_DEBOUNCE_MS = 50;

/**
 * Monotonic counter bumped every time the project globals are (re)loaded
 * (see {@link reloadGlobals}).  The source-identity short-circuit records the
 * generation under which each document was last validated; when the globals
 * change, a dependent document whose OWN text is unchanged would otherwise be
 * served stale diagnostics — comparing generations forces a fresh inference
 * with the new globals.
 */
let globalsGeneration = 0;

function publishDiagnostics(uri: string, diagnostics: Diagnostic[]): void {
  lastPublishedDiagnostics.set(uri, diagnostics);
  connection.sendDiagnostics({ uri, diagnostics });
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

let settings: HinMilSettings = { ...defaultSettings };
/** Is VS Code's built-in TypeScript/JavaScript extension active?  Reported by
 *  the hinmil client (initializationOptions + `hinmil/typescriptLanguageFeatures`);
 *  other clients never report it, so hinmil answers code definitions there. */
let typescriptLanguageFeaturesActive = false;
/** The client accepts `LocationLink`s for definitions (with the clicked
 *  range, so a whole module path is one link instead of one per word). */
let definitionLinkSupport = false;
/** The source extensions of every checked workspace folder together (module
 *  resolution and the file watchers are server-wide). */
let sourceExtensions: string[] = mergeFileSelection([]).extensions;

/**
 * A workspace folder.  A multi-root workspace has several; each has its own
 * project configuration, settings (editor settings < its `"settings"` key)
 * and file selection, and is switched off by `"enable": false` in its
 * configuration (or, with `hinmil.requiresConfig`, by having none).
 */
interface WorkspaceRoot extends SelectionRoot {
  settings: HinMilSettings;
}

/** The workspace folder paths (from `workspaceFolders`, else `rootUri`). */
let workspaceRootPaths: string[] = [];
/** The project configuration of each workspace folder, by path. */
const workspaceConfigs = new Map<string, HinMilProjectConfig>();
/** The workspace folders with their merged settings and file selection. */
let workspaceRoots: WorkspaceRoot[] = [];
/** The client reports workspace-folder changes. */
let supportsWorkspaceFolders = false;

/** The workspace folder of a document (by URI), if any. */
function rootForUri(uri: string): WorkspaceRoot | undefined {
  try {
    return uri.startsWith('file:') ? rootForFile(fileURLToPath(uri), workspaceRoots) : undefined;
  } catch {
    return undefined;
  }
}

/** The settings of a document: those of its workspace folder. */
function settingsFor(uri: string): HinMilSettings {
  return rootForUri(uri)?.settings ?? settings;
}

/** Does hinmil answer requests for this document?  Not for a file in a
 *  workspace folder that is switched off. */
function isServedDocument(uri: string): boolean {
  const root = rootForUri(uri);
  return root === undefined || root.active;
}

/**
 * A project scope: the workspace root, or a nested directory with its own
 * hinmil configuration (an application in a monorepo, such as `server/` and
 * `client/`).  Each scope has its own globals, types directory, package
 * overrides, import context and engine; a file belongs to the nearest scope
 * above it (`findScopeRoot`), within its workspace folder.  Settings and
 * the file selection belong to the workspace folder (`WorkspaceRoot`).
 */
interface ProjectScope {
  root: string;
  importCtx: ImportInferenceContext;
  engine: InferenceEngine;
  /** The globals source (globals files plus `::types` and package addenda). */
  globalsSource: string | null;
  /** All resolved absolute paths from `hinmil.globals`, used for file-change
   *  detection so editing any listed globals file triggers a reload.  The
   *  first entry is the "primary" globals file (hover linking, logging, and
   *  the `from` URI when resolving directives). */
  globalsFilePaths: string[];
}

/** Scopes by root directory, created on first use. */
const scopes = new Map<string, ProjectScope>();

/** Dependencies for the globals loader (open-doc lookup + warning output). */
const globalsLoaderDeps: GlobalsLoaderDeps = {
  getOpenDocText: (uri) => documents.get(uri)?.getText() ?? null,
  warn: (m) => connection.console.warn(m),
};

/** A scope without configuration (before the workspace root is known). */
function bareScope(): ProjectScope {
  return {
    root: '',
    importCtx: new ImportInferenceContext(documents, { warn: (m) => connection.console.warn(m) }),
    engine: new InferenceEngine(),
    globalsSource: null,
    globalsFilePaths: [],
  };
}

/** Load a scope: its configuration, globals and import context. */
function createScope(root: string): ProjectScope {
  const config = loadProjectConfig(root);
  const importCtx = new ImportInferenceContext(documents, { warn: (m) => connection.console.warn(m) });
  const engine = new InferenceEngine();
  const result = loadGlobalsFile(root, config, globalsLoaderDeps);
  let globalsSource = result.source;
  const globalsFilePaths = result.filePaths;
  importCtx.setProjectConfig(root, {
    overrides: config.overrides ?? {},
    typesDir: config.typesDir ?? DEFAULT_TYPES_DIR,
    globalsSource,
    globalsFilePath: globalsFilePaths[0] ?? null,
  });
  // Pre-walk direct deps so package-level `hinmil.globals` files are
  // visible from the very first inference (instead of only after a
  // second re-validate triggers re-discovery).
  importCtx.preloadPackageGlobalsFromWorkspace(root);
  // Append project-level auto-globals derived from `// ::types <specifier>`
  // directives in `globals.hm` (e.g. `// ::types query-builder` pulls in query-builder's
  // sidecar declarations) so aliases like `Selector` and value annotations
  // like `tables` are visible to every file the engine infers.
  const addendum = importCtx.getProjectGlobalsAddendum();
  if (addendum) {
    globalsSource = globalsSource ? `${globalsSource}\n${addendum}` : addendum;
  }
  // Append package-level globals (`package.json#hinmil.globals`) so
  // libraries can ship aliases / constraints visible to every consumer
  // file without forcing the consumer to write a `// ::types` directive.
  const pkgAddendum = importCtx.getAllPackageGlobalsAddendum();
  if (pkgAddendum) {
    globalsSource = globalsSource ? `${globalsSource}\n${pkgAddendum}` : pkgAddendum;
  }
  // The engine's globals source: every infer() call of this scope picks it up.
  engine.globalsSource = globalsSource;
  // Without a globals file the loader still returns the conventional path
  // (watched for a later create); only log a file that was actually read.
  if (result.source !== null) {
    connection.console.log(`[hinmil] Loaded globals from ${globalsFilePaths.join(', ')} (scope ${root})`);
  }
  // Phase J: warm the inline-package annotation cache in the background.
  // Each scan walks up to INLINE_PACKAGE_MAX_FILES JS files; doing this
  // synchronously inside the resolver was the dominant cold-hover cost.
  // setImmediate yields to any pending request first so we never delay
  // initialize / the first onDidOpen.
  setImmediate(() => {
    try {
      importCtx.preloadInlinePackageAnnotationsFromWorkspace(root);
      connection.console.log(`[hinmil] inline-package pre-scan complete (scope ${root})`);
    } catch (e) {
      connection.console.warn(
        `[hinmil] inline-package pre-scan failed: ${e instanceof Error ? e.message : String(e)}`,
      );
    }
  });
  return { root, importCtx, engine, globalsSource, globalsFilePaths };
}

/** The scope with this root directory (created on first use). */
function scopeAt(root: string): ProjectScope {
  let scope = scopes.get(root);
  if (!scope) {
    scope = root === '' ? bareScope() : createScope(root);
    scopes.set(root, scope);
  }
  return scope;
}

/** The scope of a document (by URI). */
function scopeFor(uri: string): ProjectScope {
  if (workspaceRoots.length === 0) return scopeAt('');
  let filePath: string;
  try {
    filePath = fileURLToPath(uri);
  } catch {
    return scopeAt(workspaceRoots[0].path);
  }
  const root = rootForFile(filePath, workspaceRoots) ?? workspaceRoots[0];
  return scopeAt(findScopeRoot(filePath, root.path));
}

/** Every scope created so far (cross-file events reach each of them). */
function allScopes(): ProjectScope[] {
  return [...scopes.values()];
}

/** Is this path one of the globals files of any scope? */
function isGlobalsFile(filePath: string): boolean {
  return allScopes().some(scope => scope.globalsFilePaths.includes(filePath));
}

/** The dependents of a file in every scope (a sidecar or module can be
 *  used by files of several scopes). */
function dependentsOf(uri: string): Set<string> | undefined {
  let out: Set<string> | undefined;
  for (const scope of allScopes()) {
    const deps = scope.importCtx.getDependents(uri);
    if (!deps || deps.size === 0) continue;
    if (!out) out = new Set<string>();
    for (const d of deps) out.add(d);
  }
  return out;
}

/** The imports of a file in every scope. */
function importsOf(uri: string): Set<string> | undefined {
  let out: Set<string> | undefined;
  for (const scope of allScopes()) {
    const imports = scope.importCtx.getImports(uri);
    if (!imports || imports.size === 0) continue;
    if (!out) out = new Set<string>();
    for (const i of imports) out.add(i);
  }
  return out;
}

/** Drop the cached inference of a file in every scope. */
function invalidateEverywhere(uri: string): void {
  for (const scope of allScopes()) scope.importCtx.invalidateFileCache(uri);
}

/** Reload the configuration and globals (on init and when a configuration
 *  or globals file changes): every scope is rebuilt on first use. */
function reloadGlobals(): void {
  if (workspaceRootPaths.length === 0) return;
  // Bump the generation so the source-identity short-circuit re-infers every
  // open document against the new globals (their own text is unchanged).
  globalsGeneration++;
  // Request-path inference results were computed under the old globals.
  requestInferCache.clear();
  // Project-file settings overrides (`"settings"` key) and file selection
  // of each workspace folder: re-merge so an edit to package.json /
  // hinmil.config.* takes effect immediately (this function runs on
  // watched-file changes for those files).
  workspaceConfigs.clear();
  for (const root of workspaceRootPaths) workspaceConfigs.set(root, loadProjectConfig(root));
  recomputeSettings();
  // Drop any cached `.hm` files so config changes take effect immediately.
  clearHmSidecarCache();
  clearInlinePackageCache();
  clearFsProbeCache();
  scopes.clear();
  for (const root of workspaceRoots) if (root.active) scopeAt(root.path);
}

// ---------------------------------------------------------------------------
// Import Inference Context — encapsulates cross-file caching & resolution
// ---------------------------------------------------------------------------

/**
 * Manages the cross-file inference cache and dependency graph.
 *
 * Centralises the fragile snapshot/restore dance that was previously
 * spread across several loose functions: every import-file inference
 * must snapshot the global method/constraint registries and the
 * type-variable counter, run a *separate* engine, restore the
 * caller's registries, then merge in the import's registrations.
 *
 * By encapsulating this in a single class the logic is easier to
 * reason about, test, and extend (e.g. with parallel inference).
 */

// ---------------------------------------------------------------------------
// Lifecycle
// ---------------------------------------------------------------------------

connection.onInitialize((params: InitializeParams): InitializeResult => {
  supportsWatchedFilesDynamicRegistration =
    params.capabilities.workspace?.didChangeWatchedFiles?.dynamicRegistration === true;
  definitionLinkSupport = params.capabilities.textDocument?.definition?.linkSupport === true;
  typescriptLanguageFeaturesActive =
    (params.initializationOptions as { typescriptLanguageFeatures?: unknown } | undefined)?.typescriptLanguageFeatures === true;
  supportsWorkspaceFolders = params.capabilities.workspace?.workspaceFolders === true;
  // The workspace folders, each with its own project configuration.  Older
  // clients only send `rootUri` (a single folder).
  if (params.workspaceFolders && params.workspaceFolders.length > 0) {
    workspaceRootPaths = params.workspaceFolders.map(folder => fileURLToPath(folder.uri));
  } else if (params.rootUri) {
    workspaceRootPaths = [fileURLToPath(params.rootUri)];
  }
  reloadGlobals();

  return {
    capabilities: {
      textDocumentSync: TextDocumentSyncKind.Incremental,
      hoverProvider: true,
      definitionProvider: true,
      completionProvider: {
        triggerCharacters: [
          '.', '/', '\'', '"', ':', '<',
          // Record-literal keys: `f ({|`, `f ({ a: 1, |`.  Only the
          // record-field providers answer these (see onCompletion), so a
          // block `{` or an argument `,` never pops up identifier noise.
          '{', ',',
          // Identifier characters — triggers completions while typing names
          ...'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_$'.split(''),
        ],
        completionItem: { labelDetailsSupport: true },
      },
      signatureHelpProvider: {
        triggerCharacters: ['(', ','],
        retriggerCharacters: [',', '[', '{'],
      },
      codeActionProvider: {
        codeActionKinds: [CodeActionKind.QuickFix],
      },
      documentSymbolProvider: true,
      referencesProvider: true,
      renameProvider: {
        prepareProvider: true,
      },
      workspace: {
        workspaceFolders: { supported: true, changeNotifications: true },
      },
    },
    serverInfo: {
      name: 'hinmil',
      version: '0.2.2',
    },
  };
});

connection.onInitialized(() => {
  connection.client.register(DidChangeConfigurationNotification.type, undefined);
  clientInitialized = true;
  if (!supportsWatchedFilesDynamicRegistration) {
    // VS Code always supports dynamic registration; other clients that do
    // not will miss on-disk dependency invalidation (open-document checking
    // and config-file watching still work).
    connection.console.warn('[hinmil] Client does not support dynamic file-watcher registration; changes to unopened dependency files will not be detected.');
  }
  syncSourceFileWatchers();
  if (supportsWorkspaceFolders) {
    // A folder added to or removed from a multi-root workspace: rebuild the
    // folders, their configuration and scopes, and recheck the open files.
    connection.workspace.onDidChangeWorkspaceFolders((event) => {
      const removed = new Set(event.removed.map(folder => fileURLToPath(folder.uri)));
      const added = event.added.map(folder => fileURLToPath(folder.uri));
      workspaceRootPaths = [
        ...workspaceRootPaths.filter(root => !removed.has(root)),
        ...added.filter(root => !workspaceRootPaths.includes(root)),
      ];
      reloadGlobals();
      refreshOpenDocumentSelection();
    });
  }
  // Fetch initial settings
  connection.workspace.getConfiguration('hinmil').then((config: Partial<HinMilSettings> | null) => {
    if (config) updateSettings(config);
  });
});

connection.onNotification('hinmil/typescriptLanguageFeatures', (params: { active?: unknown }) => {
  typescriptLanguageFeaturesActive = params?.active === true;
});

connection.onDidChangeConfiguration((change) => {
  const config = change.settings?.['hinmil'];
  if (config) {
    updateSettings(config);
  } else {
    // Some clients send empty settings; pull from workspace
    connection.workspace.getConfiguration('hinmil').then((c: Partial<HinMilSettings> | null) => {
      if (c) updateSettings(c);
    });
  }
});

/** Most recent raw settings payload from the client (VS Code settings). */
let clientSettingsLayer: unknown = {};
/** Re-merge the settings layers of every workspace folder: defaults < VS Code
 *  settings < the folder's project file (`"settings"` and `"files"` of
 *  package.json `"hinmil"` or hinmil.config.js / hinmil.config.json, refreshed
 *  by reloadGlobals). */
function recomputeSettings(): void {
  const warn = (msg: string) => connection.console.warn(msg);
  const client = typeof clientSettingsLayer === 'object' && clientSettingsLayer !== null
    ? clientSettingsLayer as { files?: unknown; requiresConfig?: unknown }
    : {};
  const requiresConfig = client.requiresConfig === true;
  workspaceRoots = workspaceRootPaths.map((root): WorkspaceRoot => {
    const config = workspaceConfigs.get(root) ?? {};
    return {
      path: root,
      active: config.enable !== false && (!requiresConfig || hasProjectConfig(root)),
      settings: mergeSettings([clientSettingsLayer, config.settings ?? {}], warn),
      fileSelection: mergeFileSelection([client.files, config.files ?? {}], warn),
    };
  });
  // Server-wide knobs (debounce, DOM typing) follow the first checked folder.
  const active = workspaceRoots.filter(root => root.active);
  const primary = active[0] ?? workspaceRoots[0];
  settings = primary?.settings ?? mergeSettings([clientSettingsLayer], warn);
  sourceExtensions = active.length > 0
    ? [...new Set(active.flatMap(root => root.fileSelection.extensions))]
    : (primary?.fileSelection ?? mergeFileSelection([client.files], warn)).extensions;
  configureModuleExtensions(sourceExtensions);
  syncSourceFileWatchers();
  // Thread the DOM/Fetch typing knobs into the engine: rebuilds the DOM
  // method bags (strict-null signatures) and invalidates the cached default
  // environment so `document`/`window`/… flip between typed TCons and `Any`.
  applyDomSettings(settings.dom);
}

function updateSettings(config: unknown): void {
  clientSettingsLayer = config;
  recomputeSettings();
  refreshOpenDocumentSelection();
}

// ---------------------------------------------------------------------------
// Watched-file registration — scoped to the effective source extensions
// ---------------------------------------------------------------------------

/** Whether the client allows dynamic `workspace/didChangeWatchedFiles` registration. */
let supportsWatchedFilesDynamicRegistration = false;
/** Set once `initialized` arrives — registrations before that are invalid. */
let clientInitialized = false;
let sourceWatcherRegistration: Disposable | undefined;
let registeredWatcherKey: string | null = null;

/**
 * (Re-)register a watcher for exactly the effective source extensions.
 * The client only watches config files statically; source files are watched
 * through this dynamic registration so custom extensions keep working while
 * avoiding a broad `**\/*` watcher. No-op when the extension set is unchanged.
 * Clients without dynamic-registration support get no source watchers (a
 * warning is logged on initialization) — config files are still watched
 * statically by the VS Code client.
 */
function syncSourceFileWatchers(): void {
  if (!clientInitialized || !supportsWatchedFilesDynamicRegistration) return;
  const extensions = sourceExtensions.map((extension) => extension.replace(/^\./, ''));
  const key = extensions.sort().join(',');
  if (key === registeredWatcherKey || extensions.length === 0) return;
  registeredWatcherKey = key;
  const globPattern = extensions.length === 1 ? `**/*.${extensions[0]}` : `**/*.{${key}}`;
  connection.client
    .register(DidChangeWatchedFilesNotification.type, { watchers: [{ globPattern }] })
    .then((registration) => {
      sourceWatcherRegistration?.dispose();
      sourceWatcherRegistration = registration;
    })
    .catch((error) => {
      registeredWatcherKey = null;
      connection.console.warn(`[hinmil] Failed to register file watchers: ${error instanceof Error ? error.message : String(error)}`);
    });
}

function refreshOpenDocumentSelection(): void {
  if (workspaceRoots.length === 0) {
    // No project root: selection is not enforced, but settings changed —
    // revalidate every open document (the pre-selection behaviour).
    for (const doc of documents.all()) {
      lastValidatedSource.delete(doc.uri);
      validateTextDocument(doc);
    }
    return;
  }
  const plan = planFileSelectionRefresh(Array.from(documents.all()), workspaceRoots);
  for (const doc of plan.clear) {
    const pending = pendingValidations.get(doc.uri);
    if (pending) clearTimeout(pending);
    pendingValidations.delete(doc.uri);
    publishDiagnostics(doc.uri, []);
  }
  for (const doc of plan.validate) {
    lastValidatedSource.delete(doc.uri);
    validateTextDocument(doc);
  }
}

// Handle file changes on disk (e.g. saving a dependency file that isn't open,
// or external edits). This ensures that when RTask.js is saved, demo2.js
// re-imports and re-validates automatically.

/**
 * Collect the open documents that should be re-validated after a `.hm`
 * sidecar changes.  Uses {@link ImportInferenceContext.getDependents} to
 * walk the reverse-dependency graph transitively — only files that
 * actually import (directly or via re-export chains) the changed sidecar
 * are returned.
 *
 * Conservative fallback: when the dep-graph has no entry for the changed
 * `.hm` URI (typical when the sidecar was never resolved yet because no
 * open file has touched it), return ALL open documents.  This matches
 * the previous blanket behaviour and protects against subtle staleness
 * for files that would resolve the sidecar on their next inference.
 * In steady state (after the first validation pass) the graph is
 * populated and the fast path is taken.
 */
function collectAffectedOpenDocs(hmUri: string): TextDocument[] {
  const directDependents = dependentsOf(hmUri);
  if (!directDependents || directDependents.size === 0) {
    return Array.from(documents.all());
  }
  const visited = new Set<string>();
  const queue: string[] = Array.from(directDependents);
  const affected: TextDocument[] = [];
  while (queue.length > 0) {
    const cur = queue.shift()!;
    if (visited.has(cur)) continue;
    visited.add(cur);
    const doc = documents.get(cur);
    if (doc) affected.push(doc);
    const transitive = dependentsOf(cur);
    if (transitive) {
      for (const t of transitive) if (!visited.has(t)) queue.push(t);
    }
  }
  return affected;
}

/**
 * Selectively invalidate the changed `.hm` sidecar + the open documents
 * that transitively depend on it, then debounce-revalidate each.
 * Uses {@link HM_REVALIDATE_DEBOUNCE_MS} (much shorter than the
 * keystroke debounce) since the user already committed an intent by
 * saving / editing the sidecar.
 */
function scheduleHmRevalidation(hmUri: string, skipUri?: string): void {
  // Evict only the changed sidecar's parsed entry; other sidecars stay warm.
  evictHmSidecar(hmUri);
  // Per-file evict of the small parseCache LRU in hmFileServices — formerly
  // a global wipe, which forced every other `.hm` to re-parse on next touch.
  clearHmParseCacheForFile(hmUri);
  // The inline-package BFS cache is workspace-wide and expensive to rebuild
  // (up to 256 files per package).  Only clear the slice tied to the
  // package this `.hm` actually belongs to.  When the .hm is a workspace
  // override (not under node_modules) the inline cache is irrelevant —
  // skip the wipe entirely.
  let inlineScope = 'none';
  try {
    const hmPath = hmUri.startsWith('file://') ? fileURLToPath(hmUri) : hmUri;
    if (/[\\/]node_modules[\\/]/.test(hmPath)) {
      const pkg = findPackageJson(hmPath);
      if (pkg) {
        clearInlinePackageCacheForPackage(pkg.pkgDir);
        inlineScope = `pkg:${path.basename(pkg.pkgDir)}`;
      } else {
        clearInlinePackageCache();
        inlineScope = 'global(no-pkg)';
      }
    }
  } catch {
    // Best-effort: a malformed URI should never block revalidation.
    clearInlinePackageCache();
    inlineScope = 'global(error)';
  }
  const direct = dependentsOf(hmUri);
  const directCount = direct?.size ?? 0;
  const affected = collectAffectedOpenDocs(hmUri);
  const fallback = !direct || direct.size === 0;
  // Transitively invalidate export caches of ALL dependents (direct and
  // indirect).  A stale intermediate export (e.g. a model file between the
  // sidecar and the open consumer) would otherwise keep serving pre-edit
  // types.  Sidecar parse artifacts themselves are stamped by doc-version /
  // mtime and re-validate lazily, so only the JS-side inference caches need
  // explicit eviction here.
  let invalidatedCount = 0;
  const visited = new Set<string>([hmUri]);
  const queue: Array<{ uri: string; depth: number }> = [{ uri: hmUri, depth: 0 }];
  while (queue.length > 0) {
    const { uri: cur, depth } = queue.shift()!;
    const deps = dependentsOf(cur);
    if (!deps) continue;
    for (const depUri of deps) {
      if (visited.has(depUri)) continue;
      visited.add(depUri);
      queue.push({ uri: depUri, depth: depth + 1 });
      invalidateEverywhere(depUri);
      lastValidatedSource.delete(depUri);
      invalidateWorkspaceExportEntry(depUri);
      invalidatedCount++;
    }
  }
  connection.console.log(
    `[hinmil] hm-revalidate ${path.basename(hmUri)}: directDeps=${directCount} ` +
    `affected=${affected.length} invalidated=${invalidatedCount} ` +
    `fallback=${fallback ? 'yes' : 'no'} inline=${inlineScope}`,
  );
  for (const doc of affected) {
    invalidateEverywhere(doc.uri);
    lastValidatedSource.delete(doc.uri);
    if (doc.uri === skipUri) continue;
    const existing = pendingValidations.get(doc.uri);
    if (existing) clearTimeout(existing);
    pendingValidations.set(
      doc.uri,
      setTimeout(() => {
        pendingValidations.delete(doc.uri);
        const d = documents.get(doc.uri);
        if (d) validateTextDocument(d);
      }, HM_REVALIDATE_DEBOUNCE_MS),
    );
  }
}

connection.onDidChangeWatchedFiles((params: DidChangeWatchedFilesParams) => {
  // Created/deleted files change module resolution: forget memoised
  // existence probes before anything below re-resolves imports.
  if (params.changes.length > 0) clearFsProbeCache();
  for (const change of params.changes) {
    // Reload globals if any of the globals files changed
    if (isGlobalsFile(fileURLToPath(change.uri))) {
      // Debounced + staggered: watcher events can arrive in bursts (e.g. a
      // git checkout touching several files) and validating every open
      // document synchronously in one tick froze all pending requests.
      scheduleGlobalsReload();
      continue;
    }

    // Also reload globals if package.json or config files changed
    if (workspaceRootPaths.length > 0) {
      const changedPath = fileURLToPath(change.uri);
      const basename = path.basename(changedPath);
      if (basename === 'package.json' || basename === 'hinmil.config.js' || basename === 'hinmil.config.json' || (DEFAULT_GLOBALS_FILES as readonly string[]).includes(basename)) {
        scheduleGlobalsReload();
      }
    }

    // `.hm` sidecars (npm package stubs, project type stubs) — selectively
    // evict the changed sidecar and re-validate only the open documents
    // that transitively depend on it (via the import dep-graph), instead
    // of blanket-invalidating every open document.
    if (change.uri.endsWith('.hm')) {
      // Dedup: if the .hm is an open document, `onDidChangeContent`
      // already fired `scheduleHmRevalidation` for this save — running
      // it again would double every cross-file validate.  Only handle
      // watched-files events for `.hm` files that are NOT open.
      if (documents.get(change.uri)) {
        continue;
      }
      scheduleHmRevalidation(change.uri);
      continue;
    }

    // Selected/custom source extensions can be dependencies even when their
    // standalone path is excluded. Do not apply include/exclude here.
    let changedExtension = '';
    try { changedExtension = path.extname(fileURLToPath(change.uri)).toLowerCase(); } catch { continue; }
    if (!sourceExtensions.includes(changedExtension) || changedExtension === '.hm') continue;
    invalidateFileAndDependents(change.uri);
  }
});

// ---------------------------------------------------------------------------
// Diagnostics — debounced to avoid noise while typing
// ---------------------------------------------------------------------------

const pendingValidations = new Map<string, ReturnType<typeof setTimeout>>();

/**
 * Invalidate the per-file caches of the changed file itself.  Cheap (O(1))
 * — safe to run on every keystroke.
 */
function invalidateFileSelf(changedUri: string): void {
  invalidateEverywhere(changedUri);
  // A change to this file or one of its dependencies makes any cached
  // inference result stale, even if the source text we last validated
  // happens to be unchanged.  Forget the fingerprint so the short-circuit
  // doesn't reuse stale data.
  lastValidatedSource.delete(changedUri);
  requestInferCache.delete(changedUri);
  // The workspace-export completion cache holds this file's exports keyed
  // by on-disk mtime; an open-editor edit doesn't touch the mtime, so
  // evict explicitly.
  invalidateWorkspaceExportEntry(changedUri);
}

/**
 * Walk the dependent graph transitively and invalidate + schedule
 * re-validation of every open file that depends on `changedUri`.
 *
 * NOT called per keystroke: editing a hub file imported by dozens of others
 * would wipe every dependent's import cache (and re-trigger the
 * workspace-export warmer) on each keystroke.  The editor-typing path runs
 * this once per debounce window (just before validating the changed file);
 * the watched-files path (on-disk changes) still runs it immediately via
 * {@link invalidateFileAndDependents}.
 */
function invalidateDependentsOf(changedUri: string): void {
  // A change to file X must invalidate every file that imports X (directly
  // OR via intermediate re-export modules), otherwise an open consumer
  // keeps reusing a stale method-registry snapshot until the LSP is
  // restarted.  Concrete case: editing `lib/RTask/RTask.js` to add
  // `// RTask#map :: ...` only marks the immediate re-exporter
  // `lib/RTask/index.js` as stale; the open consumer (`db/Repo.js`) that
  // imports through index.js never sees the new method until next process
  // start.
  const visited = new Set<string>([changedUri]);
  const queue: string[] = [changedUri];
  while (queue.length > 0) {
    const cur = queue.shift()!;
    const dependents = dependentsOf(cur);
    if (!dependents) continue;
    for (const depUri of dependents) {
      if (visited.has(depUri)) continue;
      visited.add(depUri);
      queue.push(depUri);

      invalidateEverywhere(depUri);
      lastValidatedSource.delete(depUri);
      requestInferCache.delete(depUri);
      invalidateWorkspaceExportEntry(depUri);
      // Also drop any cached published-diagnostics snapshot so the
      // source-identity short-circuit in `validateTextDocument` cannot
      // re-publish a stale snapshot for a dependent whose inputs just
      // changed.  Without this, an open consumer that happens to land
      // on a previously-validated text fingerprint would resurface old
      // diagnostics computed against the pre-invalidation imports.
      lastPublishedDiagnostics.delete(depUri);
      const depImports = importsOf(depUri);
      if (depImports) {
        for (const importedUri of depImports) {
          invalidateEverywhere(importedUri);
        }
      }

      const depDoc = documents.get(depUri);
      if (depDoc) {
        const existing = pendingValidations.get(depUri);
        if (existing) clearTimeout(existing);
        pendingValidations.set(
          depUri,
          setTimeout(() => {
            pendingValidations.delete(depUri);
            const doc = documents.get(depUri);
            if (doc) validateTextDocument(doc);
          }, settings.diagnostics.debounceMs + 100),
        );
      }
    }
  }
}

/**
 * Invalidate a file's cache and schedule re-validation of all open files
 * that depend on it (directly or transitively).
 */
function invalidateFileAndDependents(changedUri: string): void {
  invalidateFileSelf(changedUri);
  invalidateDependentsOf(changedUri);
}

/**
 * Debounced globals reload.  Typing in a globals file used to fire the full
 * reload (project config + globals file + package-globals preload + cache
 * wipes) synchronously on EVERY keystroke.  Coalesce bursts — editor
 * keystrokes as well as watcher events (a git checkout can touch several
 * config files at once) — into a single reload, then re-validate all open
 * documents with a stagger so the re-validations don't land in one
 * blocking tick.
 */
let pendingGlobalsReload: ReturnType<typeof setTimeout> | null = null;
function scheduleGlobalsReload(): void {
  if (pendingGlobalsReload) clearTimeout(pendingGlobalsReload);
  pendingGlobalsReload = setTimeout(() => {
    pendingGlobalsReload = null;
    reloadGlobals();
    scheduleValidationOfAllOpenDocs();
  }, settings.diagnostics.debounceMs);
}

/** Schedule (debounced, staggered) re-validation of every open document. */
function scheduleValidationOfAllOpenDocs(): void {
  let i = 0;
  for (const openDoc of documents.all()) {
    const openUri = openDoc.uri;
    const existing = pendingValidations.get(openUri);
    if (existing) clearTimeout(existing);
    pendingValidations.set(
      openUri,
      setTimeout(() => {
        pendingValidations.delete(openUri);
        const d = documents.get(openUri);
        if (d) validateTextDocument(d);
      }, settings.diagnostics.debounceMs + i * 50),
    );
    i++;
  }
}

documents.onDidChangeContent((change) => {
  const uri = change.document.uri;

  // Track caret position of the latest edit for the word-boundary gate
  // in `validateTextDocument`.  Only relevant for source files — `.hm`
  // sidecars have their own dedicated revalidation path.
  if (!uri.endsWith('.hm')) {
    const prev = lastSeenSource.get(uri) ?? '';
    const curr = change.document.getText();
    const offset = computeCaretOffset(prev, curr);
    lastEditPosition.set(uri, { offset, at: Date.now() });
    lastSeenSource.set(uri, curr);
  }

  // Detect if the changed document is one of the globals files (any scope)
  {
    try {
      const changedPath = fileURLToPath(uri);
      if (isGlobalsFile(changedPath)) {
        // Debounced: reloading globals synchronously on every keystroke in
        // a globals file (config re-read + package-globals preload + full
        // cache wipes + re-validation of every open document) froze the
        // server while typing there.
        scheduleGlobalsReload();
      }
    } catch { /* not a file: URI */ }
  }

  // Edits to a `.hm` sidecar in the editor: selectively invalidate only
  // open documents that transitively depend on the changed sidecar (via
  // the import dep-graph), using the short HM-revalidation debounce.
  // CRITICAL: for `.hm` URIs we MUST skip `invalidateFileAndDependents`
  // below — that path was designed for `.js` files and aggressively wipes
  // every transitive importer + each importer's full import graph.  For a
  // `.hm` sidecar that wiped 15+ unrelated caches per save, forcing a
  // 4s engine.infer on the next validate.  scheduleHmRevalidation already
  // invalidates exactly the open docs that depend on the .hm, surgically.
  if (uri.endsWith('.hm')) {
    scheduleHmRevalidation(uri, /* skipUri */ uri);
  } else {
    // Per keystroke only the cheap self-invalidation; the transitive
    // dependents walk is deferred to the debounced validation below.
    invalidateFileSelf(uri);
  }

  // Cancel any pending validation for this document
  const existing = pendingValidations.get(uri);
  if (existing) clearTimeout(existing);

  // Schedule a new validation after the user stops typing
  pendingValidations.set(
    uri,
    setTimeout(() => {
      pendingValidations.delete(uri);
      const doc = documents.get(uri);
      if (!doc) return;
      // Deferred dependents-invalidation (see invalidateDependentsOf):
      // once per debounce window instead of on every keystroke.
      if (!uri.endsWith('.hm')) invalidateDependentsOf(uri);
      validateTextDocument(doc);
    }, settings.diagnostics.debounceMs),
  );
});

function validateTextDocument(textDocument: TextDocument): void {
  if (workspaceRoots.length > 0) {
    try {
      if (!isFileChecked(fileURLToPath(textDocument.uri), workspaceRoots)) {
        publishDiagnostics(textDocument.uri, []);
        return;
      }
    } catch {
      publishDiagnostics(textDocument.uri, []);
      return;
    }
  }
  const source = textDocument.getText();

  // Word-boundary gate: if the caret of the most recent edit sits
  // *inside* an identifier (both the character before and after the
  // caret are word-chars), the user is mid-word.  Running inference now
  // would generate noisy `Unbound variable: 'foo'` diagnostics on a
  // half-typed name; defer this pass and reschedule.  After
  // {@link WORD_BOUNDARY_GATE_MS} elapsed without further edits we
  // accept the user really paused inside a partial word and validate
  // anyway (such a diagnostic is then a legitimate signal).
  //
  // Skipped for `.hm` sidecars (different validation pipeline) and when
  // no edit context is recorded yet (initial open / pre-warm).
  if (!textDocument.uri.endsWith('.hm')) {
    const editPos = lastEditPosition.get(textDocument.uri);
    if (editPos && (Date.now() - editPos.at) < WORD_BOUNDARY_GATE_MS) {
      const before = editPos.offset > 0 ? source[editPos.offset - 1] : undefined;
      const after = editPos.offset < source.length ? source[editPos.offset] : undefined;
      if (isIdentChar(before) && isIdentChar(after)) {
        // Reschedule this file's validation; do NOT publish anything.
        // Previously published diagnostics remain visible in the editor.
        const existing = pendingValidations.get(textDocument.uri);
        if (existing) clearTimeout(existing);
        pendingValidations.set(
          textDocument.uri,
          setTimeout(() => {
            pendingValidations.delete(textDocument.uri);
            const doc = documents.get(textDocument.uri);
            if (doc) validateTextDocument(doc);
          }, settings.diagnostics.debounceMs),
        );
        return;
      }
    }
  }

  // The project scope of this document: its globals, import context, engine.
  const { importCtx, engine, globalsSource, globalsFilePaths } = scopeFor(textDocument.uri);

  // Phase K: per-call circular-import counter (reset by importCtx before any inferFileAndCacheExports walks).
  importCtx.resetPerfCounters?.();

  // `.hm` annotation files have no JS body to infer — they are pure
  // declaration sources.  Run the dedicated declarations-only pipeline
  // (parse errors only; cross-sidecar reference checks are intentionally
  // skipped because realistic stubs forward-reference names that arrive
  // via other sidecars or the consumer file).
  if (textDocument.uri.endsWith('.hm')) {
    if (!settingsFor(textDocument.uri).diagnostics.enabled) {
      publishDiagnostics(textDocument.uri, []);
      lastValidatedSource.set(textDocument.uri, source);
      return;
    }
    const hmCtx: HmServiceContext = {
      findTypeDefinitions: (n) => importCtx.findTypeDefinitions(
        n, textDocument.uri, source, globalsSource, globalsFilePaths[0] ?? null,
      ),
      globals: globalsSource && globalsFilePaths[0]
        ? { source: globalsSource, uri: pathToFileURL(globalsFilePaths[0]).href }
        : null,
    };
    const hmDiags = getHmDiagnostics(textDocument.uri, source, hmCtx);
    publishDiagnostics(textDocument.uri, hmDiags);
    lastValidatedSource.set(textDocument.uri, source);
    return;
  }

  // Source-identity short-circuit: if we already validated this exact
  // text for this URI, skip re-parse + re-inference.  The cached
  // `InferenceResult` is still in `cachedResults` for code actions and
  // friends — but we MUST re-publish the diagnostics we associated with
  // this exact text, because a subsequent validation for an intermediate
  // edit may have published a different diagnostic set that VS Code
  // would otherwise leave on screen.
  if (canShortCircuit({
    prevSource: lastValidatedSource.get(textDocument.uri),
    source,
    hasCached: cachedResults.has(textDocument.uri),
    prevGeneration: validatedUnderGeneration.get(textDocument.uri),
    currentGeneration: globalsGeneration,
  })) {
    const prev = lastPublishedDiagnostics.get(textDocument.uri);
    if (prev) {
      connection.sendDiagnostics({ uri: textDocument.uri, diagnostics: prev });
    }
    return;
  }

  const resolver = importCtx.createImportResolver(textDocument.uri);
  const typeResolver = importCtx.createTypeDirectiveResolver(textDocument.uri);
  const aliasResolver = importCtx.createImportTypeAliasResolver(textDocument.uri);

  // Eagerly pre-warm direct imports so parameter inference inside this
  // file doesn't depend on the order in which the user happens to open
  // dependency files.  Without this, inferring `f(other)` where `f` is
  // an imported binding can fail to bind `other`'s type until the
  // user opens `f`'s providing module, producing inconsistent hover
  // and diagnostic output across sessions.  `inferFileAndCacheExports`
  // is idempotent and LRU-cached; on warm cache this is a cheap noop.
  // Perf: skip the loop entirely when the specifier list hasn't changed
  // since the previous validation pass.
  const specifiers = extractImportModuleSpecifiers(source);
  const prevSpecifiers = lastImportSpecifiers.get(textDocument.uri);
  const specifiersChanged = !prevSpecifiers
    || prevSpecifiers.length !== specifiers.length
    || prevSpecifiers.some((s, i) => s !== specifiers[i]);
  if (specifiersChanged) {
    for (const specifier of specifiers) {
      const targetUri = resolveImportSpecifier(specifier, textDocument.uri);
      if (targetUri && targetUri !== textDocument.uri) {
        importCtx.inferFileAndCacheExports(targetUri);
      }
    }
    lastImportSpecifiers.set(textDocument.uri, specifiers);
  }

  // Normalize array literal ASI: insert ';' before '[' at line starts
  // so that `[1,2].map(...)` on a new line is parsed as an array literal.
  const { patched, insertions } = normalizeArrayLiteralASI(source);

  // Wrap inference in a try/catch so a pathological input (e.g. a deeply
  // recursive type that exceeds MAX_DEPTH outside the unify catch, or any
  // other unexpected throw) never takes the whole language server down for
  // this file.  We surface the error as a single file-level diagnostic and
  // clear cached state so subsequent edits get a clean retry.
  let result: InferenceResult;
  try {
    result = safeEngineInfer(engine, patched, resolver, typeResolver, aliasResolver);
  } catch (e) {
    cachedResults.delete(textDocument.uri);
    lastValidatedSource.delete(textDocument.uri);
    const message = e instanceof Error ? e.message : String(e);
    connection.console.warn(`[hinmil] Inference failed for ${textDocument.uri}: ${message}`);
    publishDiagnostics(textDocument.uri, [{
      severity: DiagnosticSeverity.Warning,
      range: { start: { line: 0, character: 0 }, end: { line: 0, character: 1 } },
      message: `Inference aborted: ${message}`,
      source: 'hinmil',
    }]);
    return;
  }

  // Cache exports + full registry snapshot so a cross-file import of
  // this URI in another validation pass hits the cache in
  // `inferFileAndCacheExports` instead of re-running the engine.  Phase I.
  // Use the method snapshot captured inside `safeEngineInfer` (before the
  // builtin-originals restore) so importers see exactly what this file
  // registered, never a stale leaked override re-applied by the restore.
  importCtx.cacheExportsWithSnapshot(textDocument.uri, result.exports, lastSafeInferMethodSnapshot ?? undefined);

  // Cache the full inference result for code actions and other features
  cachedResults.set(textDocument.uri, result);
  // Record the exact source text we just validated so a follow-up
  // change-event with identical content can short-circuit.
  lastValidatedSource.set(textDocument.uri, source);
  // Record the globals generation this validation ran under, so a later
  // globals reload (which bumps the generation) defeats the short-circuit
  // even when this document's own text is unchanged.
  validatedUnderGeneration.set(textDocument.uri, globalsGeneration);

  publishDiagnostics(textDocument.uri, buildDiagnostics({
    source,
    document: textDocument,
    result,
    insertions,
    settings: settingsFor(textDocument.uri),
    circularImports: importCtx.getCircularImports(textDocument.uri),
  }));

  // Kick off (or continue) background warming of the workspace-export
  // cache for this file's directory neighbourhood, so the first
  // auto-import completion doesn't pay for a full workspace scan.
  scheduleWorkspaceExportWarming(textDocument.uri);
}

// ---------------------------------------------------------------------------
// Workspace-export cache warming (auto-import completions)
// ---------------------------------------------------------------------------

/** URIs with an active background warming loop. */
const wsWarmActive = new Set<string>();
/** Files warmed per warm call.  One file per call keeps the event-loop
 *  occupancy of a single call bounded by one file's inference time. */
const WS_WARM_FILES_PER_TICK = 1;
/** Idle gap between background warming ticks (ms). */
const WS_WARM_TICK_MS = 50;
/** Per-tick time budget: keep warming files (one at a time) until this
 *  much time elapsed, then yield the event loop. */
const WS_WARM_TICK_BUDGET_MS = 25;
/** Warming only runs after this much typing silence (any document): a
 *  single file's inference can't be preempted, so starting one while the
 *  user is typing risks stalling the next completion request behind it. */
const WS_WARM_IDLE_MS = 2000;

/** Milliseconds since the most recent edit in ANY open document. */
function msSinceLastEditAnywhere(): number {
  let latest = 0;
  for (const { at } of lastEditPosition.values()) {
    if (at > latest) latest = at;
  }
  return latest === 0 ? Number.POSITIVE_INFINITY : Date.now() - latest;
}

/**
 * Incrementally pre-compute the per-file workspace-export cache used by
 * identifier completion's auto-import suggestions.  Each tick infers a
 * few not-yet-cached files and yields the event loop, so validations and
 * completion requests interleave freely.  The loop stops when every
 * candidate file is cached; re-scheduling is cheap once warm (stat calls
 * only).
 */
function scheduleWorkspaceExportWarming(uri: string): void {
  if (!settingsFor(uri).completion.autoImports) return;
  if (uri.endsWith('.hm')) return;
  if (wsWarmActive.has(uri)) return;
  wsWarmActive.add(uri);

  const tick = () => {
    if (!documents.get(uri)) { wsWarmActive.delete(uri); return; }
    // Don't steal CPU while the user is actively typing (any document):
    // inference of a warm-tick file cannot be preempted and would delay
    // queued completion/diagnostic work.
    if (msSinceLastEditAnywhere() < WS_WARM_IDLE_MS) {
      setTimeout(tick, WS_WARM_TICK_MS);
      return;
    }
    let done = true;
    try {
      // Warm one file at a time until the per-tick budget is spent, so a
      // cheap-files stretch progresses quickly while an expensive import
      // chain still yields right after it finishes.
      const tickStart = Date.now();
      do {
        done = warmWorkspaceExports(
          uri,
          (fileUri) => scopeFor(uri).importCtx.inferFileAndCacheExports(fileUri),
          WS_WARM_FILES_PER_TICK,
        );
      } while (!done && Date.now() - tickStart < WS_WARM_TICK_BUDGET_MS);
    } catch (e) {
      debugLog('server.wsWarm', e);
    }
    if (done) { wsWarmActive.delete(uri); return; }
    setTimeout(tick, WS_WARM_TICK_MS);
  };
  setTimeout(tick, WS_WARM_TICK_MS);
}

// ---------------------------------------------------------------------------
// Array literal re-inference helper (wraps engine)
// ---------------------------------------------------------------------------

/**
 * Method registry snapshot captured by the most recent {@link safeEngineInfer}
 * call, taken at the end of `engine.infer` BEFORE built-in originals are
 * restored.  Consumed by {@link validateTextDocument} so the cached
 * cross-file snapshot reflects what the open file actually registered rather
 * than any stale leaked builtin override re-applied by the restore step.
 */
let lastSafeInferMethodSnapshot: MethodRegistrySnapshot | null = null;

/**
 * File-scoped builtin-override guard around `engine.infer`.  Captures the
 * pre-inference state of built-in method entries (e.g. `Array.every`) and
 * restores them afterwards, even on throw.  This ensures shorthand
 * annotations such as `// Array.every :: ...` in one `.js` file cannot
 * corrupt receiver-binding factories observed by unrelated files.  Only
 * globals.hm (re-processed at the start of every `engine.infer` from
 * `this.globalsSource`) may permanently mutate these entries.
 */
function safeEngineInfer(
  engine: InferenceEngine,
  source: string,
  resolver: ImportResolver,
  typeResolver: TypeDirectiveResolver,
  aliasResolver?: ImportTypeAliasResolver,
): InferenceResult {
  const snap = snapshotBuiltinOriginalEntries();
  try {
    const result = engine.infer(source, undefined, resolver, typeResolver, aliasResolver);
    // Capture the method registry exactly as it stands at the end of this
    // file's own inference — clearCustom() ran at infer start (clearing any
    // cross-request leaked builtin overrides), and only this file plus its
    // imports re-registered during the pass.  This is the authoritative
    // "what this file contributes" snapshot.  It MUST be taken before the
    // `finally` restore below, which re-applies the pre-infer builtin
    // entries (potentially a stale leaked override from a prior request)
    // and would otherwise poison the cached snapshot consumed by importers.
    lastSafeInferMethodSnapshot = snapshotMethodRegistry();
    return result;
  } finally {
    restoreBuiltinOriginalEntries(snap);
  }
}

/**
 * Re-infer source with `;` inserted before an array literal `[` that was
 * mis-parsed as computed access.  Returns the new InferenceResult + shift,
 * or null if no fix was applicable.
 */
function reinferWithArrayASIFor(engine: InferenceEngine) {
  return (
    source: string,
    closeBracketIdx: number,
    resolver: ImportResolver,
    typeResolver: TypeDirectiveResolver,
    aliasResolver?: ImportTypeAliasResolver,
  ): { result: InferenceResult; shift: number; patched: string } | null => {
    const patch = patchArrayLiteralASI(source, closeBracketIdx);
    if (!patch) return null;
    const result = safeEngineInfer(engine, patch.patched, resolver, typeResolver, aliasResolver);
    return { result, shift: patch.shift, patched: patch.patched };
  };
}

/**
 * Request-scoped inference with caching.  Returns the validation-pass result
 * when the document is validated and unchanged; otherwise consults the
 * per-URI {@link requestInferCache} keyed by the exact source text `key`,
 * inferring (and caching) only on a genuine miss.  This bounds the cost of
 * a burst of request-path inferences (signature help re-fires on every
 * keystroke while its popup is open; a completion request runs several
 * providers that each used to re-infer) to ONE inference per document
 * version.
 */
function inferForRequest(uri: string, key: string, infer: () => InferenceResult): InferenceResult {
  // A validated, unchanged document: the validation-pass result applies to
  // every request-path variant (original or ASI-patched) of that text —
  // same equivalence the hover fast path has always relied on.
  const doc = documents.get(uri);
  if (doc && lastValidatedSource.get(uri) === doc.getText()) {
    const cached = cachedResults.get(uri);
    if (cached) return cached;
  }
  const slots = requestInferCache.get(uri) ?? [];
  const hit = slots.find(s => s.key === key);
  if (hit) return hit.result;
  const result = infer();
  slots.unshift({ key, result });
  if (slots.length > REQUEST_INFER_SLOTS) slots.length = REQUEST_INFER_SLOTS;
  requestInferCache.set(uri, slots);
  return result;
}

// ---------------------------------------------------------------------------
// Hover — show inferred type at cursor position
// ---------------------------------------------------------------------------

connection.onHover((params: HoverParams): Hover | null => {
  if (!isServedDocument(params.textDocument.uri)) return null;
  const docSettings = settingsFor(params.textDocument.uri);
  const { importCtx, engine, globalsSource, globalsFilePaths } = scopeFor(params.textDocument.uri);
  if (!docSettings.hover.enabled) return null;

  const doc = documents.get(params.textDocument.uri);
  if (!doc) return null;

  const source = doc.getText();
  const offset = doc.offsetAt(params.position);

  // `.hm` files: delegate to the declarations-only hover provider.
  if (params.textDocument.uri.endsWith('.hm')) {
    const hmCtx: HmServiceContext = {
      findTypeDefinitions: (n) => importCtx.findTypeDefinitions(
        n, params.textDocument.uri, source, globalsSource, globalsFilePaths[0] ?? null,
      ),
      globals: globalsSource && globalsFilePaths[0]
        ? { source: globalsSource, uri: pathToFileURL(globalsFilePaths[0]).href }
        : null,
    };
    return reflowHover(getHmHover(params.textDocument.uri, source, offset, hmCtx));
  }

  // Only show hover on identifiers — skip keywords, braces, operators, etc.
  const cursorChar = offset < source.length ? source[offset] : '';
  const onIdentifier = /[A-Za-z0-9_$]/.test(cursorChar);
  if (!onIdentifier) {
    // Still allow alias hover in comments
    const resolver = importCtx.createImportResolver(params.textDocument.uri);
    const typeResolver = importCtx.createTypeDirectiveResolver(params.textDocument.uri);
    const aliasResolver = importCtx.createImportTypeAliasResolver(params.textDocument.uri);
    // Perf: reuse the cached `InferenceResult` from the last validation
    // pass when the document text is unchanged.  Re-running `engine.infer`
    // on every hover is the dominant LSP cost on larger files.
    const cached = lastValidatedSource.get(params.textDocument.uri) === source
      ? cachedResults.get(params.textDocument.uri)
      : undefined;
    const result = cached ?? inferForRequest(
      params.textDocument.uri, source,
      () => safeEngineInfer(engine, source, resolver, typeResolver, aliasResolver),
    );
    return reflowHover(getAliasHoverAtOffset(
      source, offset, result, params.textDocument.uri,
      resolveImportSpecifier, extractImportSpecifiers,
      (name) => importCtx.findTypeDefinitions(name, params.textDocument.uri, source, globalsSource, globalsFilePaths[0] ?? null),
    ));
  }

  const resolver = importCtx.createImportResolver(params.textDocument.uri);
  const typeResolver = importCtx.createTypeDirectiveResolver(params.textDocument.uri);
  const aliasResolver = importCtx.createImportTypeAliasResolver(params.textDocument.uri);

  // Normalize ASI for array literals and adjust offset
  const { patched: normSource, insertions } = normalizeArrayLiteralASI(source);
  const normOffset = mapOffset(offset, insertions);

  // Perf: reuse the cached `InferenceResult` from the last validation
  // pass when the document text is unchanged.  `validateTextDocument`
  // caches the result of `engine.infer(patched, ...)` where `patched` is
  // the normalizeArrayLiteralASI output, so reusing it is safe whenever
  // the original (pre-normalize) source matches.
  const cachedHover = lastValidatedSource.get(params.textDocument.uri) === source
    ? cachedResults.get(params.textDocument.uri)
    : undefined;
  let result = cachedHover ?? inferForRequest(
    params.textDocument.uri, normSource,
    () => safeEngineInfer(engine, normSource, resolver, typeResolver, aliasResolver),
  );

  // Find the most specific node whose range contains the offset
  let bestType: import('./hm/types').Type | null = null;
  let rawBestType: import('./hm/types').Type | null = null;
  let bestStart = -1;
  let bestEnd = -1;
  // True when `bestType` is the frozen annotation snapshot for a parameter.
  // Rule #1: the signature wins — such a type must render with its OWN
  // variable letters, so we must NOT seed the pretty-printer from the
  // enclosing scope (which would re-letter the signature's `a` to `b`).
  let bestFromFrozen = false;

  for (const [start, { type, end }] of result.nodeTypes) {
    if (start <= normOffset && normOffset < end && start > bestStart) {
      bestType = result.substitution.apply(type);
      rawBestType = type;
      bestStart = start;
      bestEnd = end;
    }
  }

  // Declaration site of a polymorphic top-level binding: show its generic
  // scheme (freshly instantiated) rather than the live substitution-applied
  // node type, which a downstream call site may have specialized (e.g. a
  // generic `getPath` leaking a concrete `{ address :: { zip :: b } }`).
  // Shared helper — keeps `rawBestType` (the constraint source) intact.
  ({ bestType, rawBestType } = applyDeclaredSchemeDisplay(result, bestStart, bestType, rawBestType));
  // A parameter's declared type is the annotation the user wrote.  Body
  // inference may bind the annotation's row / value vars (e.g. `Object.keys`
  // closing an open `{ a }` row to `{}`), poisoning the live-substituted
  // type above.  When the cursor is on such an annotated parameter, prefer the
  // frozen annotation snapshot so hover always shows the signature form.
  //
  // EXCEPTION: only STRUCTURED annotations (records, arrays, unions, applied
  // constructors) need this protection.  A bare type variable has no structure
  // to protect, and a "frozen" bare var is often not a user annotation at all
  // but a caller / overload-provided expected type (e.g. an overloaded `map`
  // callback parameter) that only resolves to a concrete shape — such as
  // `Pair Number (f a)` — AFTER unification.  Rendering that frozen snapshot
  // raw would show a meaningless `a`, so keep the live substitution-applied
  // type in that case.
  if (bestStart >= 0 && result.frozenParamType?.has(bestStart)) {
    const frozen = result.frozenParamType.get(bestStart)!;
    if (frozen.tag !== 'TVar') {
      bestType = frozen;
      rawBestType = frozen;
      bestFromFrozen = true;
    }
  }
  // Replace any rigid skolem constants (minted while checking annotated
  // bodies) with the annotation's display letters so hover never shows `§N`.
  if (bestType && result.skolemDisplayNames && result.skolemDisplayNames.size > 0) {
    bestType = scrubSkolems(bestType, result.skolemDisplayNames);
  }

  // Suppress hover when the cursor is on a property access on an
  // unconstrained type variable (e.g. `x.name` where `x :: a`).
  // We check bestStart (the property node's start offset) rather than
  // normOffset (the cursor position) so suppression works regardless of
  // which character within the property name the cursor is on.
  if (bestStart >= 0 && result.unconstrainedPropAccesses.has(bestStart)) {
    bestType = null;
    rawBestType = null;
    bestStart = -1;
  }

  // Fallback for array literal member access
  let arrayShift = 0;
  if ((!bestType || bestType.tag === 'TVar') && validIdentLooksLikeArrayMethod(normSource, normOffset)) {
    const arrFix = tryArrayLiteralReinfer(normSource, normOffset, resolver, typeResolver, engine, reinferWithArrayASIFor(engine));
    if (arrFix) {
      result = arrFix.result;
      bestType = arrFix.bestType;
      rawBestType = null; // no raw type needed for array reinfer
      bestStart = arrFix.bestStart;
      arrayShift = arrFix.shift;
    }
  }

  // Find the smallest function type that STRICTLY encloses the hovered node.
  // Its variable letters seed the hover rendering so a variable shared with
  // the enclosing scope (e.g. `f :: a -> b` and its `result`) shows the same
  // letter everywhere in the body, and sibling body-local bindings (`let n`,
  // `let xs`) get distinct, source-ordered letters instead of colliding.
  let scopeType: import('./hm/types').Type | null = null;
  if (!bestFromFrozen && bestType && bestStart >= 0 && bestEnd >= 0) {
    scopeType = buildScopeSeedType(result, result.substitution, bestStart, bestEnd);
  }

  return reflowHover(buildHover({
    source, offset, result, bestType, rawBestType, bestStart, arrayShift,
    scopeType,
    inferredTypeStyle: docSettings.display.typeVariables,
    uri: params.textDocument.uri,
    resolveImportSpecifier,
    extractImportSpecifiers,
    getImportedRawSignature: (spec, name, fromUri) => importCtx.getImportedRawSignature(spec, name, fromUri),
    findTypeDefinitions: (name) => importCtx.findTypeDefinitions(name, params.textDocument.uri, source, globalsSource, globalsFilePaths[0] ?? null),
    positionAt: (o: number) => doc.positionAt(o),
  }));
});

// ---------------------------------------------------------------------------
// Definition — go to definition for type aliases in annotations, and (see
// `navigation.definitions`) for module paths, imports and local names
// ---------------------------------------------------------------------------

/** hinmil answers code definitions (see `navigation.definitions`). */
function codeDefinitionsEnabled(uri: string): boolean {
  const mode = settingsFor(uri).navigation.definitions;
  return mode === 'always' || (mode === 'auto' && !typescriptLanguageFeaturesActive);
}

/** Source of a file for definitions: the open editor buffer, else the disk. */
function readSourceForDefinition(filePath: string): string | null {
  const open = documents.get(pathToFileURL(filePath).href);
  if (open) return open.getText();
  try {
    return fs.readFileSync(filePath, 'utf-8');
  } catch {
    return null;
  }
}

/** A code definition as LSP result.  With link support each target is a
 *  `LocationLink` whose origin is the clicked text (a whole module path,
 *  a whole identifier); VS Code underlines exactly that.  Otherwise plain
 *  `Location`s, and the editor falls back to its own word range. */
function toDefinitionResult(def: CodeDefinition, source: string): Location[] | LocationLink[] {
  const origin = {
    start: positionAt(source, def.origin.start),
    end: positionAt(source, def.origin.end),
  };
  const links: LocationLink[] = [];
  for (const target of def.targets) {
    const text = readSourceForDefinition(target.path);
    if (text === null) continue;
    const range = { start: positionAt(text, target.start), end: positionAt(text, target.end) };
    links.push(LocationLink.create(pathToFileURL(target.path).href, range, range, origin));
  }
  return definitionLinkSupport
    ? links
    : links.map(link => Location.create(link.targetUri, link.targetRange));
}

connection.onDefinition((params: DefinitionParams): Location | Location[] | LocationLink[] | null => {
  if (!isServedDocument(params.textDocument.uri)) return null;
  const { importCtx, engine, globalsSource, globalsFilePaths } = scopeFor(params.textDocument.uri);
  const doc = documents.get(params.textDocument.uri);
  if (!doc) return null;

  const source = doc.getText();
  const offset = doc.offsetAt(params.position);

  // `.hm` files: delegate to the declarations-only definition provider.
  if (params.textDocument.uri.endsWith('.hm')) {
    const hmCtx: HmServiceContext = {
      findTypeDefinitions: (n) => importCtx.findTypeDefinitions(
        n, params.textDocument.uri, source, globalsSource, globalsFilePaths[0] ?? null,
      ),
      globals: globalsSource && globalsFilePaths[0]
        ? { source: globalsSource, uri: pathToFileURL(globalsFilePaths[0]).href }
        : null,
    };
    return getHmDefinition(params.textDocument.uri, source, offset, hmCtx);
  }

  // --- Code: module paths, imported names, local names (syntactic, no
  //     inference needed).  Comments are left to the type navigation below. ---
  if (codeDefinitionsEnabled(params.textDocument.uri) && !isOffsetInComment(source, offset)) {
    const definition = findCodeDefinition(source, params.textDocument.uri, offset, {
      includeLocal: true,
      readSource: readSourceForDefinition,
    });
    if (definition) {
      const found = toDefinitionResult(definition, source);
      if (found.length > 0) return found;
    }
  }

  const resolver = importCtx.createImportResolver(params.textDocument.uri);
  const typeResolver = importCtx.createTypeDirectiveResolver(params.textDocument.uri);
  const aliasResolver = importCtx.createImportTypeAliasResolver(params.textDocument.uri);
  // Perf: reuse cached inference result when source is unchanged.
  const cachedDef = lastValidatedSource.get(params.textDocument.uri) === source
    ? cachedResults.get(params.textDocument.uri)
    : undefined;
  const result = cachedDef ?? safeEngineInfer(engine, source, resolver, typeResolver, aliasResolver);

  const word = getWordAt(source, offset);

  // --- ::types directive: navigate to the referenced file ---
  const typeDirectives = extractTypeDirectivesWithLocations(source);
  for (const dir of typeDirectives) {
    if (offset >= dir.start && offset <= dir.end) {
      const resolved = resolveTypeDirectiveSpecifier(dir.specifier, params.textDocument.uri);
      if (resolved) {
        return { uri: pathToFileURL(resolved).href, range: { start: { line: 0, character: 0 }, end: { line: 0, character: 0 } } };
      }
    }
  }

  if (!word) return null;

  // Build globals context for definition lookup
  const globalsCtx = globalsSource && globalsFilePaths[0]
    ? { source: globalsSource, uri: pathToFileURL(globalsFilePaths[0]).href }
    : null;

  // --- Uppercase words: try type-alias / constructor definition first ---
  if (/^[A-Z]/.test(word)) {
    // Trigger when cursor is inside a comment annotation, a ::narrow directive, or a ::constraint directive
    const inAnnotation = isOffsetInAnyAnnotation(result.annotations, result.annotationsByOffset, offset)
      || isOffsetInComment(source, offset);
    const narrowType = getNarrowDirectiveTypeAtOffset(source, offset);
    const inConstraint = isOffsetInConstraintDirective(source, offset);

    // Also trigger for uppercase identifiers in code that are known type constructors
    // (e.g. Box, RTask) — this improves go-to-definition for CJS require() imports
    // where the built-in JS/TS provider may not follow the require correctly.
    const inCode = !inAnnotation && !narrowType && !inConstraint;
    if (!inCode || result.annotations.get(word)?.scheme) {
      const typeName = narrowType || word;
      const location = findTypeDefinitionLocation(typeName, source, params.textDocument.uri, result, globalsCtx);
      if (location) return location;

      // Fallback: search globals + imported sidecars for a matching type
      // declaration.  Honours `// ::prefer Name from <specifier>` to pick
      // the right one when multiple definitions exist.  This makes
      // go-to-definition work for types like `Prop` from query-builder that
      // are visible to inference but live only in a sidecar `.hm` file.
      const defs = importCtx.findTypeDefinitions(
        typeName, params.textDocument.uri, source, globalsSource, globalsFilePaths[0] ?? null,
      );
      if (defs.length > 0) {
        const prefer = require('./commentParser').extractPreferDirectives(source).get(typeName);
        const matchesPrefer = (origin: string): boolean => {
          if (!prefer) return false;
          if (origin === prefer) return true;
          return origin.startsWith(prefer + ' ') || origin === `<${prefer}>`;
        };
        // When a `// ::prefer` directive picks a single source, return
        // only that location.  Otherwise return ALL matching definitions
        // so the editor can show e.g. both the base sidecar declaration
        // and a project-level override.
        const candidates = prefer
          ? defs.filter(d => matchesPrefer(d.origin))
          : defs;
        const chosen = candidates.length > 0 ? candidates : defs;
        const locations: Location[] = [];
        for (const def of chosen) {
          if (!def.sourcePath) continue;
          try {
            const text = fs.readFileSync(def.sourcePath, 'utf-8');
            locations.push(Location.create(pathToFileURL(def.sourcePath).href, {
              start: positionAt(text, def.commentStart),
              end: positionAt(text, def.commentEnd),
            }));
          } catch { /* unreadable — skip */ }
        }
        if (locations.length === 1) return locations[0];
        if (locations.length > 1) return locations;
      }
    }
  }

  // --- Constraint method: navigate to constraint definition for .method on constrained types ---
  // Find the most specific node at the cursor offset to look up constraint method signatures
  let bestStart = -1;
  for (const [start, { end }] of result.nodeTypes) {
    if (start <= offset && offset < end && start > bestStart) {
      bestStart = start;
    }
  }
  if (bestStart >= 0) {
    const methodSig = result.methodSignatures.get(bestStart);
    if (methodSig) {
      // Method signatures from constraints are formatted as "[ConstraintName] method :: ..."
      const constraintMatch = /^\[([A-Z]\w*)\]/.exec(methodSig);
      if (constraintMatch) {
        const constraintName = constraintMatch[1];
        const location = findTypeDefinitionLocation(constraintName, source, params.textDocument.uri, result, globalsCtx);
        if (location) return location;
      }
    }
  }

  // --- Import identifiers: skip — the built-in JS/TS service handles
  //     go-to-definition for regular imports.  Only intervene for type-
  //     related definitions (handled above). ---
  const importSpecifiers = extractImportSpecifiers(source);
  if (importSpecifiers.has(word)) return null;

  // --- Fallback: annotation name → code definition ---
  // When cursor is on the function name inside an HM annotation comment
  // (e.g. `// intercalate :: ...`), navigate to the code definition.
  // For regular code identifiers, return null and let the built-in
  // JS/TS language service handle go-to-definition (avoids duplicates).
  const allGroups = collectReferences(source, result);
  for (const [, group] of allGroups) {
    if (group.annotationNameStart !== undefined && group.annotationNameEnd !== undefined) {
      if (offset >= group.annotationNameStart && offset <= group.annotationNameEnd) {
        const defLoc = group.locations.find(loc => loc.isDefinition);
        if (defLoc) {
          return {
            uri: params.textDocument.uri,
            range: {
              start: doc.positionAt(defLoc.start),
              end: doc.positionAt(defLoc.end),
            },
          };
        }
      }
    }
  }

  return null;
});

// ---------------------------------------------------------------------------
// Code Actions — quick-fix suggestions
// ---------------------------------------------------------------------------

connection.onCodeAction((params: CodeActionParams): CodeAction[] => {
  if (!isServedDocument(params.textDocument.uri)) return [];
  const doc = documents.get(params.textDocument.uri);
  if (!doc) return [];
  if (params.textDocument.uri.endsWith('.hm')) return [];

  const result = cachedResults.get(params.textDocument.uri);
  if (!result) return [];

  const source = doc.getText();
  const importSpecifierMap = extractImportSpecifiers(source);

  const ctx: CodeActionContext = {
    result,
    textDocument: doc,
    inferredTypeStyle: settingsFor(params.textDocument.uri).display.typeVariables,
    importSpecifierMap,
  };

  return getCodeActions(params, ctx);
});

// ---------------------------------------------------------------------------
// Document Symbols — outline / breadcrumbs
// ---------------------------------------------------------------------------

connection.onDocumentSymbol((params: DocumentSymbolParams): DocumentSymbol[] => {
  if (!isServedDocument(params.textDocument.uri)) return [];
  const doc = documents.get(params.textDocument.uri);
  if (!doc) return [];

  const source = doc.getText();

  // `.hm` files: flat list of annotation declarations (no inference cache).
  if (params.textDocument.uri.endsWith('.hm')) {
    return getHmDocumentSymbols(params.textDocument.uri, source);
  }

  const result = cachedResults.get(params.textDocument.uri);
  if (!result) return [];

  const ctx: DocumentSymbolContext = {
    result,
    inferredTypeStyle: settingsFor(params.textDocument.uri).display.typeVariables,
  };

  return getDocumentSymbols(source, ctx);
});

// ---------------------------------------------------------------------------
// Completion — delegate to ./completion module
// ---------------------------------------------------------------------------

/** The first provider result that is not empty (providers run lazily). */
function firstNonEmpty(providers: Array<() => CompletionItem[]>): CompletionItem[] {
  for (const provider of providers) {
    const items = provider();
    if (items.length > 0) return items;
  }
  return [];
}

connection.onCompletion((params: CompletionParams): CompletionItem[] => {
  if (!isServedDocument(params.textDocument.uri)) return [];
  const docSettings = settingsFor(params.textDocument.uri);
  const { importCtx, engine, globalsSource, globalsFilePaths } = scopeFor(params.textDocument.uri);
  if (!docSettings.completion.enabled) return [];

  const doc = documents.get(params.textDocument.uri);
  if (!doc) return [];

  // Completion in `.hm` files is not yet implemented — the JS-oriented
  // completers all expect runnable JS source and would produce noise.
  if (params.textDocument.uri.endsWith('.hm')) return [];

  const source = doc.getText();
  const offset = doc.offsetAt(params.position);
  const uri = params.textDocument.uri;

  const ctx: CompletionContext = {
    engine,
    createImportResolver: (fromUri: string) => importCtx.createImportResolver(fromUri),
    createTypeDirectiveResolver: (fromUri: string) => importCtx.createTypeDirectiveResolver(fromUri),
    createImportTypeAliasResolver: (fromUri: string) => importCtx.createImportTypeAliasResolver(fromUri),
    inferFileAndCacheExports: (fileUri: string) => importCtx.inferFileAndCacheExports(fileUri),
    inferredTypeStyle: docSettings.display.typeVariables,
    autoImports: docSettings.completion.autoImports,
    cachedResult: cachedResults.get(uri),
    getImportedRawSignature: (spec, name, fromUri) => importCtx.getImportedRawSignature(spec, name, fromUri),
    // One completion request runs several providers that each may infer the
    // current (or ASI-patched) source; the request cache collapses those to
    // at most one inference per source variant.
    inferSource: (src: string) => inferForRequest(uri, src, () => safeEngineInfer(
      engine,
      src,
      importCtx.createImportResolver(uri),
      importCtx.createTypeDirectiveResolver(uri),
      importCtx.createImportTypeAliasResolver(uri),
    )),
  };

  // `{` / `,` as trigger: only record-field completions (object-literal
  // arguments, destructuring patterns, returned records, import braces).
  const trigger = params.context?.triggerKind === CompletionTriggerKind.TriggerCharacter
    ? params.context.triggerCharacter
    : undefined;
  if (trigger === '{' || trigger === ',') {
    return getImportSpecifierCompletions(source, offset, uri, ctx)
      ?? firstNonEmpty([
        () => getDestructuringCompletions(source, offset, uri, ctx),
        () => getSumTypeRecordCompletions(source, offset, uri, ctx),
        () => getTypeAliasRecordCompletions(source, offset, uri, ctx),
        () => getJSXStyleKeyCompletions(source, offset, ctx) ?? [],
      ]);
  }

  // --- Import specifier completion: import { | } from './module' ---
  const importSpecifierItems = getImportSpecifierCompletions(source, offset, uri, ctx);
  if (importSpecifierItems) return importSpecifierItems;

  // --- Import path completion: from './|' ---
  const importPathItems = getImportPathCompletions(source, offset, uri, ctx);
  if (importPathItems) return importPathItems;

  // --- Destructuring completion: const { | } = expr ---
  const destructuringItems = getDestructuringCompletions(source, offset, uri, ctx);
  if (destructuringItems.length > 0) return destructuringItems;

  // --- sumtype factory record completion: return { | } ---
  const sumTypeItems = getSumTypeRecordCompletions(source, offset, uri, ctx);
  if (sumTypeItems.length > 0) return sumTypeItems;

  // --- Type alias record completion: return { | } or => ({ | }) ---
  const aliasRecordItems = getTypeAliasRecordCompletions(source, offset, uri, ctx);
  if (aliasRecordItems.length > 0) return aliasRecordItems;

  // --- Directive keyword completion: // ::i| → ignore, ignore-file, ... ---
  const directiveItems = getDirectiveCompletions(source, offset);
  if (directiveItems.length > 0) return directiveItems;

  // --- ::types path completion: // ::types ./|  or  // ::types ../lib/| ---
  const typeDirectivePathItems = getTypeDirectivePathCompletions(source, offset, uri);
  if (typeDirectivePathItems) return typeDirectivePathItems;

  // --- Annotation type completion: // name :: Num| ---
  const annotationTypeItems = getAnnotationTypeCompletions(source, offset, uri, ctx);
  if (annotationTypeItems.length > 0) return annotationTypeItems;

  // --- Annotation name completion: // myF| → suggest existing JS bindings ---
  const annotationNameItems = getAnnotationNameCompletions(source, offset, uri, ctx);
  if (annotationNameItems.length > 0) return annotationNameItems;

  // --- Bracket string completion: expr["| or expr['| ---
  const bracketStringItems = getBracketStringCompletions(source, offset, uri, ctx);
  if (bracketStringItems.length > 0) return bracketStringItems;

  // --- JSX prop completion: <Badge l| ---
  const jsxPropItems = getJSXPropCompletions(source, offset, uri, ctx);
  if (jsxPropItems.length > 0) return jsxPropItems;

  // --- CSS property completion inside style={{ … }} (array = final,
  //     even when empty — key positions must not fall through) ---
  const jsxStyleKeyItems = getJSXStyleKeyCompletions(source, offset, ctx);
  if (jsxStyleKeyItems) return jsxStyleKeyItems;

  // --- JSX component-name completion: <Badg| ---
  const jsxComponentItems = getJSXComponentCompletions(source, offset, uri, ctx);
  if (jsxComponentItems.length > 0) return jsxComponentItems;

  // --- Table-selector completion: PascalCase([ | ]) or PascalCase(["i| ---
  const tableSelectorItems = getTableSelectorCompletions(source, offset, uri, ctx);
  if (tableSelectorItems.length > 0) return tableSelectorItems;

  // --- Dot completion: expr.| ---
  const dotIdx = offset - 1;
  if (dotIdx >= 0 && source[dotIdx] === '.') {
    return getDotCompletions(source, offset, dotIdx, uri, ctx);
  }

  // --- Identifier completion with type info + auto-import ---
  return getIdentifierCompletions(source, offset, uri, ctx);
});

// ---------------------------------------------------------------------------
// Signature Help — show parameter info when typing function arguments
// ---------------------------------------------------------------------------

connection.onSignatureHelp((params: SignatureHelpParams): SignatureHelp | null => {
  if (!isServedDocument(params.textDocument.uri)) return null;
  const { importCtx, engine, globalsSource, globalsFilePaths } = scopeFor(params.textDocument.uri);
  if (!settingsFor(params.textDocument.uri).signatureHelp.enabled) return null;

  const doc = documents.get(params.textDocument.uri);
  if (!doc) return null;
  if (params.textDocument.uri.endsWith('.hm')) return null;

  const uri = params.textDocument.uri;
  const resolver = importCtx.createImportResolver(uri);
  const typeResolver = importCtx.createTypeDirectiveResolver(uri);
  const aliasResolver = importCtx.createImportTypeAliasResolver(uri);

  return provideSignatureHelp({
    source: doc.getText(),
    offset: doc.offsetAt(params.position),
    engine,
    resolver,
    typeResolver,
    importTypeAliasResolver: aliasResolver,
    reinferWithArrayASI: reinferWithArrayASIFor(engine),
    // Signature help re-fires on every keystroke while its popup is open;
    // route inference through the request cache so an unchanged document
    // version never pays for a second inference.
    inferSource: (src) => inferForRequest(uri, src, () => safeEngineInfer(engine, src, resolver, typeResolver, aliasResolver)),
  });
});

// ---------------------------------------------------------------------------
// References / Rename — delegated to ./services/rename
// ---------------------------------------------------------------------------

connection.onReferences((params: ReferenceParams): Location[] => {
  if (!isServedDocument(params.textDocument.uri)) return [];
  const doc = documents.get(params.textDocument.uri);
  if (!doc) return [];
  if (params.textDocument.uri.endsWith('.hm')) return [];
  return provideReferences(doc, params, cachedResults.get(params.textDocument.uri));
});

connection.onPrepareRename((params: PrepareRenameParams): { range: Range; placeholder: string } | null => {
  if (!isServedDocument(params.textDocument.uri)) return null;
  const doc = documents.get(params.textDocument.uri);
  if (!doc) return null;
  if (params.textDocument.uri.endsWith('.hm')) return null;
  return providePrepareRename(doc, params, cachedResults.get(params.textDocument.uri));
});

connection.onRenameRequest((params: RenameParams): WorkspaceEdit | null => {
  if (!isServedDocument(params.textDocument.uri)) return null;
  const doc = documents.get(params.textDocument.uri);
  if (!doc) return null;
  if (params.textDocument.uri.endsWith('.hm')) return null;
  return provideRename(doc, params, cachedResults.get(params.textDocument.uri));
});

// ---------------------------------------------------------------------------
// Start
// ---------------------------------------------------------------------------

// Clean up per-document state when a document is closed so that
// `cachedResults` and import-context caches don't accumulate over the
// lifetime of the server.  We also clear any pending diagnostics so the
// editor doesn't keep showing stale ones for a file that's no longer open.
documents.onDidClose((event) => {
  const uri = event.document.uri;
  cachedResults.delete(uri);
  lastValidatedSource.delete(uri);
  requestInferCache.delete(uri);
  validatedUnderGeneration.delete(uri);
  lastPublishedDiagnostics.delete(uri);
  lastImportSpecifiers.delete(uri);
  lastSeenSource.delete(uri);
  lastEditPosition.delete(uri);
  const pending = pendingValidations.get(uri);
  if (pending) {
    clearTimeout(pending);
    pendingValidations.delete(uri);
  }
  // Only invalidate the import-context entry if no other open file
  // depends on it; otherwise keep it cached so cross-file inference
  // still works.
  const dependents = dependentsOf(uri);
  const stillNeeded = dependents && Array.from(dependents).some(d => documents.get(d));
  if (!stillNeeded) {
    invalidateEverywhere(uri);
  }
  connection.sendDiagnostics({ uri, diagnostics: [] });
});

// Background pre-warm on open: as soon as the user opens a file, fire-and-
// forget infer its direct imports so the file-level cache is warm by the
// time the first hover or completion request arrives.  Without this, the
// only thing that warms the import cache is `validateTextDocument`, which
// only runs after the keystroke debounce (default 500ms) — so a hover that
// lands within that window walks the entire import graph synchronously on
// the hover request thread (observed: ~10s on large repos).
//
// `inferFileAndCacheExports` is idempotent + LRU-cached: subsequent
// validations / hovers re-use the warmed entries.  We also seed
// `lastImportSpecifiers` so the validation pre-warm loop sees no change
// and skips its own redundant pass.
documents.onDidOpen((event) => {
  const doc = event.document;
  const uri = doc.uri;
  if (uri.endsWith('.hm')) return;
  if (!uri.endsWith('.js') && !uri.endsWith('.mjs') && !uri.endsWith('.cjs') && !uri.endsWith('.jsx')) return;
  setImmediate(() => {
    try {
      const source = doc.getText();
      const specifiers = extractImportModuleSpecifiers(source);
      for (const specifier of specifiers) {
        try {
          const targetUri = resolveImportSpecifier(specifier, uri);
          if (targetUri && targetUri !== uri) {
            scopeFor(uri).importCtx.inferFileAndCacheExports(targetUri);
          }
        } catch { /* per-specifier failure must not break pre-warm */ }
      }
      // Seed so the validation pre-warm loop sees specifiers unchanged.
      lastImportSpecifiers.set(uri, specifiers);
    } catch (e) {
      connection.console.warn(
        `[hinmil] pre-warm failed for ${uri}: ${e instanceof Error ? e.message : String(e)}`,
      );
    }
  });
});

documents.listen(connection);
connection.listen();
