import * as vscode from "vscode";
import { CircuitMetadata, ProfileSummary } from "./profile";

let statusBarItem: vscode.StatusBarItem | undefined;

export function activateStatus(context: vscode.ExtensionContext) {
  statusBarItem = vscode.window.createStatusBarItem(
    vscode.StatusBarAlignment.Right,
    100
  );
  statusBarItem.command = "xark.showCircuitStats";
  statusBarItem.tooltip = "Click for circuit statistics";
  context.subscriptions.push(statusBarItem);
}

export function deactivateStatus() {
  statusBarItem?.dispose();
  statusBarItem = undefined;
}

export function updateStatus(
  summary: ProfileSummary | null,
  meta: CircuitMetadata | null
) {
  if (!statusBarItem) return;

  if (summary && summary.totalConstraints > 0) {
    statusBarItem.text = `$(graph) ${fmtCount(summary.totalConstraints)}`;
    statusBarItem.tooltip = buildTooltip(summary, meta);
    statusBarItem.show();
  } else if (summary && summary.totalConstraints === 0) {
    statusBarItem.text = "$(graph) 0 constraints";
    statusBarItem.tooltip = "No constraints emitted";
    statusBarItem.show();
  } else {
    statusBarItem.hide();
  }
}

function buildTooltip(
  summary: ProfileSummary,
  meta: CircuitMetadata | null
): string {
  const lines: string[] = [];
  lines.push(`${summary.totalConstraints} total constraints`);
  if (meta) {
    lines.push(`${meta.num_vars} variables`);
    const pubCount = meta.inputs.filter((i) => i.role === "public").length;
    const privCount = meta.inputs.filter((i) => i.role === "private").length;
    lines.push(`${pubCount} public, ${privCount} private inputs`);
    if (meta.num_witness_ops > 0) {
      lines.push(`${meta.num_witness_ops} witness-gen ops`);
    }
    lines.push(`field: ${meta.field}`);
  }
  lines.push("");
  lines.push("Click for full stats");
  return lines.join(" • ");
}

export function showCircuitStats(
  summary: ProfileSummary | null,
  meta: CircuitMetadata | null
) {
  if (!summary && !meta) {
    vscode.window.showInformationMessage(
      "xark: No circuit data available. Run `xark check --profile` first."
    );
    return;
  }

  const items: vscode.QuickPickItem[] = [];
  if (summary) {
    items.push({
      label: `$(graph) ${summary.totalConstraints} constraints`,
      description: "R1CS rows",
    });
  }
  if (meta) {
    items.push({
      label: `$(symbol-variable) ${meta.num_vars} variables`,
      description: "Total declared",
    });
    const pubCount = meta.inputs.filter((i) => i.role === "public").length;
    const privCount = meta.inputs.filter((i) => i.role === "private").length;
    items.push({
      label: `$(lock) ${pubCount} public, $(key) ${privCount} private inputs`,
      description: "Input visibility",
    });
    if (meta.num_witness_ops > 0) {
      items.push({
        label: `$(run-all) ${meta.num_witness_ops} witness-gen ops`,
        description: "Solver steps",
      });
    }
    items.push({
      label: `$(symbol-field) field: ${meta.field}`,
      description: "Proving field",
    });
  }

  vscode.window.showQuickPick(items, {
    title: "xark — Circuit Overview",
    placeHolder: "Circuit statistics",
  });
}

function fmtCount(n: number): string {
  if (n >= 1_000_000) return `${(n / 1_000_000).toFixed(1)}M`;
  if (n >= 1_000) return `${(n / 1_000).toFixed(1)}K`;
  return n.toLocaleString();
}
