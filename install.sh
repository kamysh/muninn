#!/usr/bin/env bash
# install.sh — build and register muninn with Claude Code
#
# Installs via `nix profile install` so the Nix profile itself is the GC root.
# The binaries live in ~/.nix-profile/bin/ and will not break after `nix store gc`.
set -euo pipefail

PROJECT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "Installing muninn into Nix profile..."
# Use standard Nix profile upgrade/install flow. If muninn isn't installed yet,
# upgrade will fail and we fall back to install.
if ! nix profile upgrade --impure muninn; then
  nix profile install --impure "$PROJECT_DIR#muninn"
fi

BIN_DIR="${HOME}/.nix-profile/bin"

echo "Registering muninn-mcp with Claude Code..."
claude mcp remove muninn --scope user 2>/dev/null || true
claude mcp add --scope user muninn "${BIN_DIR}/muninn-mcp"

echo ""
echo "Done. Next steps:"
echo "  1. Start the indexer:  systemctl --user enable --now muninn-index"
echo "  2. Add a repo:    muninn add /path/to/repo"
echo "  3. Start Claude Code — muninn search tools are now available"
