import * as vscode from "vscode";
import { formatInline, hasHints, LineCost, linesForFile, ProfileSummary } from "./profile";

let decorationType: vscode.TextEditorDecorationType | undefined;

export function activateAnnotations(_context: vscode.ExtensionContext) {
  decorationType = vscode.window.createTextEditorDecorationType({
    after: {
      margin: "0 0 0 2em",
      color: new vscode.ThemeColor("editorCodeLens.foreground"),
      fontStyle: "normal",
      fontWeight: "normal",
    },
    isWholeLine: true,
  });
}

export function deactivateAnnotations() {
  decorationType?.dispose();
  decorationType = undefined;
}

/** Update gutter annotations for the given profile and visible editors. */
export function updateAnnotations(
  summary: ProfileSummary | null,
  maxLines: number
) {
  if (!decorationType) return;

  for (const editor of vscode.window.visibleTextEditors) {
    if (editor.document.languageId !== "rust") continue;
    applyToEditor(editor, summary, maxLines);
  }
}

function applyToEditor(
  editor: vscode.TextEditor,
  summary: ProfileSummary | null,
  maxLines: number
) {
  if (!summary) {
    editor.setDecorations(decorationType!, []);
    return;
  }

  const filePath = editor.document.uri.fsPath;
  const lineCosts = linesForFile(summary, filePath);
  if (lineCosts.size === 0) {
    editor.setDecorations(decorationType!, []);
    return;
  }

  const decorations: vscode.DecorationOptions[] = [];
  let count = 0;
  for (const [line, cost] of lineCosts) {
    if (count++ >= maxLines) break;
    const range = new vscode.Range(line - 1, 0, line - 1, 0);
    const hintPrefix = hasHints(cost) ? "⚡ " : "";
    const text = hintPrefix + formatInline(cost);
    decorations.push({
      range,
      renderOptions: {
        after: {
          contentText: text,
          color: dimColor(cost.total),
        },
      },
    });
  }

  editor.setDecorations(decorationType!, decorations);
}

/** Fade annotation color as constraint count decreases. */
function dimColor(total: number): string {
  if (total >= 100) return "rgba(255, 255, 255, 0.45)";
  if (total >= 50) return "rgba(255, 255, 255, 0.35)";
  if (total >= 10) return "rgba(255, 255, 255, 0.28)";
  return "rgba(255, 255, 255, 0.20)";
}
