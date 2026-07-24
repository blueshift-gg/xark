import * as vscode from "vscode";
import * as path from "path";
import * as fs from "fs";
import { loadProfile, ProfileSummary, LineCost, formatInline, formatKinds, linesForFile, hasHints, CircuitMetadata, loadMetadata } from "./profile";
import {
  activateAnnotations,
  deactivateAnnotations,
  updateAnnotations,
} from "./annotations";
import { activateStatus, deactivateStatus, updateStatus, showCircuitStats } from "./status";
import {
  cmdCheck,
  cmdBuild,
  cmdProfile,
  cmdProve,
  cmdSetup,
  cmdInspect,
} from "./commands";
import { injectConfig } from "./config";

// ---- State ------------------------------------------------------------------

let currentSummary: ProfileSummary | null = null;
let currentMetadata: CircuitMetadata | null = null;
let profileWatcher: fs.FSWatcher | undefined;
let showAnnotations = true;
let profileRefreshTimer: ReturnType<typeof setTimeout> | undefined;

// ---- Activation -------------------------------------------------------------

export function activate(context: vscode.ExtensionContext) {
  // UI modules
  activateAnnotations(context);
  activateStatus(context);

  // Commands
  context.subscriptions.push(
    vscode.commands.registerCommand("xark.check", cmdCheck()),
    vscode.commands.registerCommand("xark.build", cmdBuild()),
    vscode.commands.registerCommand("xark.profile", cmdProfile()),
    vscode.commands.registerCommand("xark.prove", cmdProve()),
    vscode.commands.registerCommand("xark.setup", cmdSetup()),
    vscode.commands.registerCommand("xark.inspect", cmdInspect()),
    vscode.commands.registerCommand("xark.injectConfig", () => injectConfig()),
    vscode.commands.registerCommand("xark.toggleProfileAnnotations", toggleAnnotations),
    vscode.commands.registerCommand("xark.refreshProfile", () => loadAndUpdate()),
    vscode.commands.registerCommand("xark.showCircuitStats", () =>
      showCircuitStats(currentSummary, currentMetadata)
    ),
  );

  // CodeLens: per-function constraint breakdown
  context.subscriptions.push(
    vscode.languages.registerCodeLensProvider(
      { language: "rust" },
      new ConstraintCodeLensProvider()
    )
  );

  // Hover: detailed constraint info on hover
  context.subscriptions.push(
    vscode.languages.registerHoverProvider(
      { language: "rust" },
      new ConstraintHoverProvider()
    )
  );

  // Watch for profile.json changes in workspace target/xark dirs
  setupProfileWatchers(context);

  // Refresh on file save (debounced)
  context.subscriptions.push(
    vscode.workspace.onDidSaveTextDocument((doc) => {
      if (doc.languageId !== "rust") return;
      if (vscode.workspace.getConfiguration("xark").get<boolean>("profileOnSave")) {
        // Don't run xark check here (rust-analyzer does that). Just debounce
        // a profile reload — wait for xark check to finish and write profile.json.
        scheduleProfileRefresh();
      }
    })
  );

  // Refresh when active editor changes (reload profile for the new crate)
  context.subscriptions.push(
    vscode.window.onDidChangeActiveTextEditor(() => {
      loadAndUpdate();
    })
  );

  // Initial load
  loadAndUpdate();
}

export function deactivate() {
  deactivateAnnotations();
  deactivateStatus();
  if (profileWatcher) profileWatcher.close();
  if (profileRefreshTimer) clearTimeout(profileRefreshTimer);
}

// ---- Profile loading --------------------------------------------------------

function findProfileJson(): string | undefined {
  const editor = vscode.window.activeTextEditor;
  if (!editor) {
    // Fallback: search workspace folders
    for (const ws of vscode.workspace.workspaceFolders ?? []) {
      const found = findInDir(ws.uri.fsPath);
      if (found) return found;
    }
    return undefined;
  }

  // Walk up from the active file to find the crate root, then look for
  // target/xark/<pkg>/profile.json
  let dir = path.dirname(editor.document.uri.fsPath);
  while (true) {
    const found = findInDir(dir);
    if (found) return found;
    const parent = path.dirname(dir);
    if (parent === dir) break;
    dir = parent;
  }

  // Fallback: workspace root
  const ws = vscode.workspace.getWorkspaceFolder(editor.document.uri);
  if (ws) {
    const found = findInDir(ws.uri.fsPath);
    if (found) return found;
  }

  return undefined;
}

function findInDir(crateDir: string): string | undefined {
  const xarkDir = path.join(crateDir, "target", "xark");
  if (!fs.existsSync(xarkDir)) return undefined;

  // List subdirectories, look for profile.json
  let entries: fs.Dirent[];
  try {
    entries = fs.readdirSync(xarkDir, { withFileTypes: true });
  } catch {
    return undefined;
  }

  for (const entry of entries) {
    if (!entry.isDirectory()) continue;
    if (entry.name === "debug" || entry.name === "release") continue;
    const profilePath = path.join(xarkDir, entry.name, "profile.json");
    if (fs.existsSync(profilePath)) return profilePath;
  }

  return undefined;
}

function loadAndUpdate() {
  const profilePath = findProfileJson();
  if (profilePath) {
    currentSummary = loadProfile(profilePath);
    currentMetadata = loadMetadata(profilePath);
  } else {
    currentSummary = null;
    currentMetadata = null;
  }
  updateUI(currentSummary, currentMetadata);
}

function updateUI(summary: ProfileSummary | null, meta: CircuitMetadata | null) {
  if (showAnnotations) {
    updateAnnotations(summary, maxLines());
  } else {
    updateAnnotations(null, maxLines());
  }
  updateStatus(summary, meta);
  // Notify CodeLens to re-query
  codeLensesChanged.fire();
}

// ---- Profile watchers -------------------------------------------------------

function setupProfileWatchers(context: vscode.ExtensionContext) {
  // Watch for profile.json creation in workspace target/xark dirs.
  // When rust-analyzer runs `xark check --profile`, it writes profile.json.
  // We detect this and refresh annotations.
  for (const ws of vscode.workspace.workspaceFolders ?? []) {
    const xarkDir = path.join(ws.uri.fsPath, "target", "xark");
    if (fs.existsSync(xarkDir)) {
      watchDirRecursive(xarkDir, context);
    }
  }

  // Also watch for the creation of target/xark itself (first build)
  const watcher = vscode.workspace.createFileSystemWatcher(
    "**/target/xark/*/profile.json"
  );
  watcher.onDidCreate(() => scheduleProfileRefresh());
  watcher.onDidChange(() => scheduleProfileRefresh());
  context.subscriptions.push(watcher);
}

function watchDirRecursive(dir: string, context: vscode.ExtensionContext) {
  try {
    const entries = fs.readdirSync(dir, { withFileTypes: true });
    for (const entry of entries) {
      if (entry.isDirectory()) {
        watchDirRecursive(path.join(dir, entry.name), context);
      }
    }
  } catch {
    // directory may not exist yet
  }
}

function scheduleProfileRefresh() {
  if (profileRefreshTimer) clearTimeout(profileRefreshTimer);
  profileRefreshTimer = setTimeout(() => {
    loadAndUpdate();
  }, 500); // debounce: wait for file write to complete
}

// ---- Toggle annotations -----------------------------------------------------

function toggleAnnotations() {
  showAnnotations = !showAnnotations;
  vscode.window.showInformationMessage(
    `xark: constraint-cost annotations ${showAnnotations ? "shown" : "hidden"}`
  );
  updateUI(currentSummary, currentMetadata);
}

function maxLines(): number {
  return vscode.workspace
    .getConfiguration("xark")
    .get<number>("annotationMaxLines") ?? 100;
}

// ---- CodeLens provider ------------------------------------------------------

const codeLensesChanged = new vscode.EventEmitter<void>();

class ConstraintCodeLensProvider implements vscode.CodeLensProvider {
  private _onDidChangeCodeLenses = codeLensesChanged;
  public readonly onDidChangeCodeLenses = this._onDidChangeCodeLenses.event;

  refresh() {
    this._onDidChangeCodeLenses.fire();
  }

  provideCodeLenses(
    document: vscode.TextDocument
  ): vscode.CodeLens[] {
    if (!currentSummary) return [];

    const filePath = document.uri.fsPath;
    const lineCosts = linesForFile(currentSummary, filePath);
    const lenses: vscode.CodeLens[] = [];
    const text = document.getText();

    // Find fn definitions and check whether any constraints fall within their
    // body range (approximate brace matching). If none, flag as dead code.
    const fnRegex = /(?:pub\s+)?fn\s+(\w+)\s*[^{]*\{/g;
    let match: RegExpExecArray | null;
    while ((match = fnRegex.exec(text)) !== null) {
      const fnName = match[1];
      const openBrace = match.index + match[0].length - 1; // position of `{`
      const openLine = document.positionAt(openBrace).line + 1;

      // Find matching `}` by counting braces
      const closeLine = findClosingBraceLine(text, openBrace, document);
      if (!closeLine) continue;

      // Count constraints on lines between open and close braces
      let total = 0;
      for (const [line, cost] of lineCosts) {
        if (line >= openLine && line <= closeLine) {
          total += cost.total;
        }
      }

      if (total > 0) continue; // skip — has constraints

      lenses.push(
        new vscode.CodeLens(
          new vscode.Range(openLine - 1, 0, openLine - 1, 0),
          {
            title: "$(circle-slash) 0 constraints — dead code",
            command: "",
            tooltip:
              `"${fnName}" produces no R1CS constraints and is not part of the circuit`,
          }
        )
      );
    }

    return lenses;
  }
}

/** Find the 1-based line of the matching `}` for an opening `{` at byte offset. */
function findClosingBraceLine(
  text: string,
  openBrace: number,
  document: vscode.TextDocument
): number | undefined {
  let depth = 0;
  for (let i = openBrace; i < text.length; i++) {
    if (text[i] === "{") depth++;
    else if (text[i] === "}") {
      depth--;
      if (depth === 0) return document.positionAt(i).line + 1;
    }
  }
  return undefined;
}

// ---- Hover provider ---------------------------------------------------------

class ConstraintHoverProvider implements vscode.HoverProvider {
  provideHover(
    document: vscode.TextDocument,
    position: vscode.Position
  ): vscode.Hover | undefined {
    if (!currentSummary) return undefined;

    const filePath = document.uri.fsPath;
    const lineCosts = linesForFile(currentSummary, filePath);
    const line = position.line + 1;
    const cost = lineCosts.get(line);

    if (!cost) return undefined;

    const lines: string[] = [];
    lines.push(`**${cost.total} constraints** on this line`);
    lines.push("");

    // Kind breakdown
    lines.push("| Kind | Count |");
    lines.push("|------|-------|");
    for (const [kind, count] of [...cost.kinds.entries()].sort(
      (a, b) => b[1] - a[1]
    )) {
      lines.push(`| ${kind} | ${count} |`);
    }

    // Function chain
    if (cost.chains.size > 0) {
      lines.push("");
      lines.push("**Function chains:**");
      for (const [chain, count] of [...cost.chains.entries()].sort(
        (a, b) => b[1] - a[1]
      )) {
        lines.push(`- \`${chain}\` (${count})`);
      }
    }

    // Hint warning
    if (hasHints(cost)) {
      lines.push("");
      lines.push(
        "⚡ **Hint constraints** — ensure this value is pinned by an `assert_eq` " +
        "or it will be under-constrained."
      );
    }

    if (cost.src) {
      lines.push("");
      lines.push(`\`\`\`rust\n${cost.src}\n\`\`\``);
    }

    return new vscode.Hover(new vscode.MarkdownString(lines.join("\n")));
  }
}

