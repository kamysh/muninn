#!/usr/bin/env bash
# install.sh — build and register muninn with Claude Code
#
# Installs via `nix profile install` so the Nix profile itself is the GC root.
# The binaries live in ~/.nix-profile/bin/ and will not break after `nix store gc`.
set -euo pipefail

PROJECT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "Installing muninn into Nix profile..."
nix profile install "$PROJECT_DIR"

BIN_DIR="${HOME}/.nix-profile/bin"

echo "Registering muninn-mcp with Claude Code..."
claude mcp add muninn "${BIN_DIR}/muninn-mcp"

echo ""
echo "Done. Next steps:"
echo "  1. Start the indexer:  systemctl --user enable --now muninn-index"
echo "  2. Register a repo:    muninn register /path/to/repo"
echo "  3. Start Claude Code — muninn search tools are now available"