import * as vscode from "vscode";
import * as cp from "child_process";
import * as path from "path";

// ---- Shared helpers ---------------------------------------------------------

/** Find the crate root for a given source file. */
function findCrateRoot(uri: vscode.Uri): string | undefined {
  // Look for Cargo.toml walking up from the file
  let dir = path.dirname(uri.fsPath);
  while (true) {
    const cargoToml = path.join(dir, "Cargo.toml");
    try {
      // We need sync stat; use a try/catch around fs access
      const fs = require("fs");
      fs.accessSync(cargoToml);
      return dir;
    } catch {
      const parent = path.dirname(dir);
      if (parent === dir) break;
      dir = parent;
    }
  }
  // Fallback: workspace folder
  const ws = vscode.workspace.getWorkspaceFolder(uri);
  return ws?.uri.fsPath;
}

function xarkBinary(): string {
  return vscode.workspace.getConfiguration("xark").get<string>("binary") ?? "xark";
}

function runXark(
  args: string[],
  cwd: string,
  output: vscode.OutputChannel
): Promise<number> {
  return new Promise((resolve) => {
    const bin = xarkBinary();
    output.appendLine(`$ ${bin} ${args.join(" ")}`);
    const child = cp.spawn(bin, args, { cwd });

    child.stdout.on("data", (data: Buffer) => output.append(data.toString()));
    child.stderr.on("data", (data: Buffer) => output.append(data.toString()));

    child.on("close", (code) => {
      if (code !== 0) {
        output.appendLine(`\r\nxark exited with code ${code}`);
      }
      resolve(code ?? 1);
    });

    child.on("error", (err) => {
      output.appendLine(`\r\nFailed to run xark: ${err.message}`);
      resolve(1);
    });
  });
}

let outputChannel: vscode.OutputChannel | undefined;

function getOutput(): vscode.OutputChannel {
  if (!outputChannel) {
    outputChannel = vscode.window.createOutputChannel("xark");
  }
  outputChannel.show(true);
  return outputChannel;
}

// ---- Command implementations ------------------------------------------------

export function cmdCheck(crateDir?: string) {
  return async () => {
    const cwd = crateDir ?? findCrateDir();
    if (!cwd) return;
    const out = getOutput();
    out.clear();
    await runXark(["check", ".", "--profile"], cwd, out);
    // Trigger a refresh of profile data
    vscode.commands.executeCommand("xark.refreshProfile");
  };
}

export function cmdBuild(crateDir?: string) {
  return async () => {
    const cwd = crateDir ?? findCrateDir();
    if (!cwd) return;
    const out = getOutput();
    out.clear();
    await runXark(["build", "."], cwd, out);
  };
}

export function cmdProfile(crateDir?: string) {
  return async () => {
    const cwd = crateDir ?? findCrateDir();
    if (!cwd) return;
    const out = getOutput();
    out.clear();
    await runXark(["profile", ".", "--json"], cwd, out);
  };
}

export function cmdProve(crateDir?: string) {
  return async () => {
    const cwd = crateDir ?? findCrateDir();
    if (!cwd) return;
    // Prompt for inputs
    const inputs = await vscode.window.showInputBox({
      prompt: "Circuit inputs as JSON (e.g. {\"secret\": 3, \"result\": 27})",
      placeHolder: '{"secret": 3, "result": 27}',
    });
    if (inputs === undefined) return; // user cancelled
    const out = getOutput();
    out.clear();
    await runXark(["prove", ".", "--inputs", inputs], cwd, out);
  };
}

export function cmdSetup(crateDir?: string) {
  return async () => {
    const cwd = crateDir ?? findCrateDir();
    if (!cwd) return;
    const out = getOutput();
    out.clear();
    await runXark(["setup", "."], cwd, out);
  };
}

export function cmdInspect(crateDir?: string) {
  return async () => {
    const cwd = crateDir ?? findCrateDir();
    if (!cwd) return;
    const out = getOutput();
    out.clear();
    await runXark(["inspect", "."], cwd, out);
  };
}

function findCrateDir(): string | undefined {
  const editor = vscode.window.activeTextEditor;
  if (editor) {
    return findCrateRoot(editor.document.uri);
  }
  // Fallback to first workspace folder
  const ws = vscode.workspace.workspaceFolders?.[0];
  return ws?.uri.fsPath;
}
