import * as vscode from "vscode";
import * as fs from "fs";
import * as path from "path";

/** Write (or offer to write) rust-analyzer.toml + .vscode/settings.json
 *  so xark check runs on save. */
export async function injectConfig(crateDir?: string): Promise<void> {
  const cwd = crateDir ?? findCrateDir();
  if (!cwd) {
    vscode.window.showErrorMessage("xark: no crate directory found.");
    return;
  }

  const raToml = path.join(cwd, "rust-analyzer.toml");
  const vsCodeDir = path.join(cwd, ".vscode");
  const vsCodeSettings = path.join(vsCodeDir, "settings.json");

  const raContent = [
    "# Run xark's subset validator on save so unsupported constructs show inline.",
    "# `--profile` writes per-line constraint costs to target/xark/ for the",
    "# xark-vscode extension to render as gutter annotations.",
    "[check]",
    'overrideCommand = ["xark", "check", ".", "--message-format=json", "--profile"]',
    "",
  ].join("\n");

  const vsCodeContent = JSON.stringify(
    {
      "rust-analyzer.check.overrideCommand": [
        "xark",
        "check",
        ".",
        "--message-format=json",
        "--profile",
      ],
    },
    null,
    2
  );

  const actions: string[] = [];
  if (!fs.existsSync(raToml)) actions.push("rust-analyzer.toml");
  if (!fs.existsSync(vsCodeSettings)) actions.push(".vscode/settings.json");

  if (actions.length === 0) {
    vscode.window.showInformationMessage(
      "xark: rust-analyzer config already exists for this crate."
    );
    return;
  }

  const choice = await vscode.window.showInformationMessage(
    `xark: Write editor config for this crate? (${actions.join(", ")})`,
    "Yes",
    "No"
  );

  if (choice !== "Yes") return;

  try {
    if (actions.includes("rust-analyzer.toml")) {
      fs.writeFileSync(raToml, raContent, "utf-8");
    }
    if (actions.includes(".vscode/settings.json")) {
      fs.mkdirSync(vsCodeDir, { recursive: true });
      // Don't overwrite existing; merge if simple object
      let existing: any = {};
      if (fs.existsSync(vsCodeSettings)) {
        try {
          existing = JSON.parse(fs.readFileSync(vsCodeSettings, "utf-8"));
        } catch { /* ignore malformed json, will overwrite */ }
      }
      existing["rust-analyzer.check.overrideCommand"] = [
        "xark", "check", ".", "--message-format=json", "--profile",
      ];
      fs.writeFileSync(
        vsCodeSettings,
        JSON.stringify(existing, null, 2) + "\n",
        "utf-8"
      );
    }
    vscode.window.showInformationMessage(
      `xark: Wrote ${actions.join(", ")} — reload the window for rust-analyzer to pick it up.`
    );
  } catch (err: any) {
    vscode.window.showErrorMessage(`xark: failed to write config: ${err.message}`);
  }
}

function findCrateDir(): string | undefined {
  const editor = vscode.window.activeTextEditor;
  if (editor) {
    let dir = path.dirname(editor.document.uri.fsPath);
    while (true) {
      if (fs.existsSync(path.join(dir, "Cargo.toml"))) return dir;
      const parent = path.dirname(dir);
      if (parent === dir) break;
      dir = parent;
    }
  }
  return vscode.workspace.workspaceFolders?.[0]?.uri.fsPath;
}
