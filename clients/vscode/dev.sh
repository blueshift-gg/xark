#!/usr/bin/env bash
# Get the latest extension source into your VS Code.
#
# Run this AFTER the agent edits anything under clients/vscode/src/.
# Then reload the VS Code window (it will prompt you, or press Ctrl+R).
#
#   ./clients/vscode/dev.sh
#
set -euo pipefail
cd "$(dirname "$0")"

# Make sure deps are installed (no-op after the first time).
if [ ! -d node_modules ]; then
  echo "→ installing dependencies (first run only)…"
  npm install --silent
fi

echo "→ compiling TypeScript…"
npx tsc -p ./

echo "→ packaging .vsix…"
npx --yes @vscode/vsce package --allow-missing-repository >/dev/null

vsix=$(ls -t xark-vscode-*.vsix | head -1)
echo "→ installing $vsix into VS Code…"
code --install-extension "$vsix" --force >/dev/null

echo
echo "✓ Done. Reload VS Code (Ctrl+R) to pick up the changes."
