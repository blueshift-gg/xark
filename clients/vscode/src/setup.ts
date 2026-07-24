import * as vscode from "vscode";
import * as cp from "child_process";
import * as fs from "fs";
import * as path from "path";

/**
 * Zero-config first-run experience.
 *
 * On activation, detect whether the workspace contains an xark circuit crate.
 * If it does, ensure:
 *   1. The `xark` binary is available on PATH.
 *   2. rust-analyzer's `check.overrideCommand` is wired to `xark check --profile`.
 *   3. A `profile.json` exists (bootstrapped by a one-shot `xark check --profile`).
 *
 * The goal: install the extension, open a circuit crate, see diagnostics — no
 * manual wiring, no command-palette incantations.
 */

/** Is this workspace folder an xark circuit crate?
 *
 *  A circuit crate depends on `xark` and uses the `#[circuit]` attribute
 *  macro on a real fn (not inside a string/comment, e.g. the CLI's scaffold
 *  template). Both signals are required so we don't light up the extension for
 *  the toolchain's own crates (cli, gadgets, …) that merely reference xark. */
export function isXarkCrate(folder: string): boolean {
  const cargoPath = path.join(folder, "Cargo.toml");
  let cargo: string;
  try {
    cargo = fs.readFileSync(cargoPath, "utf-8");
  } catch {
    return false;
  }
  // A dependency line like `xark = { ... }` or `xark = "0.1"`.
  // `m` flag so `^` matches any line; won't match `xark-keccak` inside a name.
  if (!/^\s*xark\s*=/m.test(cargo)) return false;

  // Confirm there's a real `#[circuit]` attribute in src/. Strip Rust string
  // literals and line comments first so templates/doc-comments don't fool us
  // (the CLI's `xark init` template literally contains `#[circuit]` in a string).
  const srcDir = path.join(folder, "src");
  const rsFiles: string[] = [];
  walkRs(srcDir, rsFiles);
  return rsFiles.some((f) => {
    try {
      const src = stripNoise(fs.readFileSync(f, "utf-8"));
      return /#\[\s*circuit\s*\]/.test(src);
    } catch {
      return false;
    }
  });
}

/** Recursively collect `*.rs` files under `dir`. */
function walkRs(dir: string, out: string[]): void {
  let entries: fs.Dirent[];
  try {
    entries = fs.readdirSync(dir, { withFileTypes: true });
  } catch {
    return;
  }
  for (const e of entries) {
    const p = path.join(dir, e.name);
    if (e.isDirectory()) walkRs(p, out);
    else if (e.name.endsWith(".rs")) out.push(p);
  }
}

/** Remove Rust string literals and line comments so attribute scanning doesn't
 *  match text inside strings or docs. (Crude but sufficient for detection.) */
function stripNoise(s: string): string {
  return s
    .replace(/r#*"[\s\S]*?"#*/g, "") // raw strings r"..." / r#"..."#
    .replace(/"(?:\\[\s\S]|[^"\\])*"/g, "") // regular strings (incl. \<newline>)
    .replace(/\/\/.*/g, ""); // line comments (incl. `///`, `//!`)
}

/** Does `xark --version` succeed? Returns the version string, or null. */
export function xarkVersion(): string | null {
  const bin = vscode.workspace.getConfiguration("xark").get<string>("binary") ?? "xark";
  try {
    const out = cp.spawnSync(bin, ["--version"], { encoding: "utf-8" });
    if (out.status === 0) {
      return out.stdout.trim() || out.stderr.trim();
    }
  } catch {
    /* not on PATH */
  }
  return null;
}

/** Does the workspace's rust-analyzer config already point at xark?
 *
 *  Checks both `.vscode/settings.json` (VS Code) and `rust-analyzer.toml`
 *  (editor-agnostic). Parses the JSON settings properly so any reformatting
 *  (multi-line arrays, reordered keys) still matches — a raw `/xark.*check/`
 *  regex would miss pretty-printed arrays where `xark` and `check` land on
 *  separate lines, causing the enable-prompt to re-fire forever. */
export function hasXarkOverride(folder: string): boolean {
  // 1. VS Code settings.json — parse and inspect the actual override value.
  try {
    const settings = JSON.parse(
      fs.readFileSync(path.join(folder, ".vscode", "settings.json"), "utf-8")
    );
    const cmd = settings["rust-analyzer.check.overrideCommand"];
    if (Array.isArray(cmd) && cmd.some((s) => s === "xark")) {
      return true;
    }
  } catch {
    /* missing or malformed — fall through to the toml check */
  }

  // 2. rust-analyzer.toml — the editor-agnostic form `xark init` also writes.
  //    It's TOML, not JSON, so a newline-tolerant regex is the pragmatic check.
  try {
    const toml = fs.readFileSync(path.join(folder, "rust-analyzer.toml"), "utf-8");
    if (/xark[\s\S]*check/.test(toml)) {
      return true;
    }
  } catch {
    /* no toml */
  }

  return false;
}

/** Write the rust-analyzer override into `.vscode/settings.json`, merging
 *  any existing config rather than clobbering it. */
export function writeOverride(folder: string): void {
  const vsCodeDir = path.join(folder, ".vscode");
  const settingsPath = path.join(vsCodeDir, "settings.json");
  fs.mkdirSync(vsCodeDir, { recursive: true });

  let existing: Record<string, unknown> = {};
  try {
    existing = JSON.parse(fs.readFileSync(settingsPath, "utf-8"));
  } catch {
    /* missing or malformed — start fresh */
  }
  existing["rust-analyzer.check.overrideCommand"] = [
    "xark", "check", ".", "--message-format=json", "--profile",
  ];
  fs.writeFileSync(settingsPath, JSON.stringify(existing, null, 2) + "\n", "utf-8");
}

/** Bootstrap a `profile.json` by running `xark check --profile` once.
 *  Resolves to the exit code (0 = success). */
export function bootstrapProfile(folder: string): Promise<number> {
  return new Promise((resolve) => {
    const bin = vscode.workspace.getConfiguration("xark").get<string>("binary") ?? "xark";
    const child = cp.spawn(bin, ["check", ".", "--profile"], { cwd: folder });
    child.on("close", (code) => resolve(code ?? 1));
    child.on("error", () => resolve(1));
  });
}

/** Run the full first-run experience. Safe to call on every activation — it
 *  short-circuits once everything is in place. */
export async function runFirstRunExperience(
  context: vscode.ExtensionContext
): Promise<void> {
  const autoConfigure = vscode.workspace
    .getConfiguration("xark")
    .get<boolean>("autoConfigure", true);
  if (!autoConfigure) return;

  // Find the first workspace folder that is an xark crate.
  const folders = vscode.workspace.workspaceFolders ?? [];
  const xarkFolder = folders.map((f) => f.uri.fsPath).find(isXarkCrate);
  if (!xarkFolder) return; // not an xark workspace — stay dormant

  // --- Step 1: binary check --------------------------------------------------
  const version = xarkVersion();
  if (!version) {
    // Only nag once per workspace.
    const key = `xark.binaryMissing:${xarkFolder}`;
    if (!context.globalState.get<boolean>(key)) {
      context.globalState.update(key, true);
      const choice = await vscode.window.showWarningMessage(
        "xark: The `xark` CLI was not found on PATH. Install it to enable inline circuit diagnostics.",
        "Install instructions",
        "Don't show again"
      );
      if (choice === "Don't show again") {
        context.globalState.update(key, true);
      } else if (choice === "Install instructions") {
        vscode.env.openExternal(
          vscode.Uri.parse("https://github.com/blueshift-gg/xark#installation")
        );
      }
    }
    return; // nothing else we can do without the binary
  }

  // --- Step 2: config wiring -------------------------------------------------
  if (!hasXarkOverride(xarkFolder)) {
    const key = `xark.configOffered:${xarkFolder}`;
    if (!context.globalState.get<boolean>(key)) {
      const choice = await vscode.window.showInformationMessage(
        "xark: Enable inline constraint diagnostics for this circuit crate?",
        "Enable",
        "Not now"
      );
      if (choice === "Enable") {
        writeOverride(xarkFolder);
        const reload = await vscode.window.showInformationMessage(
          "xark: Configured. Reload the window so rust-analyzer picks it up.",
          "Reload now"
        );
        if (reload === "Reload now") {
          vscode.commands.executeCommand("workbench.action.reloadWindow");
        }
      }
      // Remember we asked (regardless of answer) so we don't nag every reload.
      context.globalState.update(key, true);
    }
  }

  // --- Step 3: bootstrap profile.json ----------------------------------------
  // If there's no profile yet (first open), generate one so annotations appear
  // immediately rather than waiting for the first save-triggered check.
  const profilePath = await findProfileJson(xarkFolder);
  if (!profilePath) {
    await bootstrapProfile(xarkFolder);
  }
}

/** Locate `target/xark/<pkg>/profile.json` under a crate dir. */
async function findProfileJson(crateDir: string): Promise<string | null> {
  const xarkDir = path.join(crateDir, "target", "xark");
  let entries: fs.Dirent[];
  try {
    entries = fs.readdirSync(xarkDir, { withFileTypes: true });
  } catch {
    return null;
  }
  for (const entry of entries) {
    if (!entry.isDirectory()) continue;
    if (entry.name === "debug" || entry.name === "release") continue;
    const p = path.join(xarkDir, entry.name, "profile.json");
    if (fs.existsSync(p)) return p;
  }
  return null;
}
