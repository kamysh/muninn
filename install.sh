#!/usr/bin/env bash
# install.sh — build muninn as a static binary and register it with Claude Code.
#
# Builds the fully-static (musl) binaries via `nix build .#muninn-static` and
# installs them to ~/.local/bin. The MCP server is registered at that path, and
# the systemd user unit (muninn-index.service) execs %h/.local/bin/muninn-index.
# Static binaries carry no /nix/store references, so they survive `nix store gc`
# without the Nix profile having to be a GC root.
set -euo pipefail

PROJECT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BIN_DIR="${HOME}/.local/bin"
mkdir -p "$BIN_DIR"

echo "Building static muninn binaries (nix build .#muninn-static)..."
OUT="$(nix build "${PROJECT_DIR}#muninn-static" --no-link --print-out-paths)"

echo "Installing binaries to ${BIN_DIR}..."
install -m 755 "${OUT}/bin/muninn"       "${BIN_DIR}/muninn"
install -m 755 "${OUT}/bin/muninn-mcp"   "${BIN_DIR}/muninn-mcp"
install -m 755 "${OUT}/bin/muninn-index" "${BIN_DIR}/muninn-index"

echo "Registering muninn-mcp with Claude Code..."
claude mcp remove muninn --scope user 2>/dev/null || true
claude mcp add --scope user muninn "${BIN_DIR}/muninn-mcp"

echo ""
echo "Done. Next steps:"
echo "  1. Start the indexer:  systemctl --user enable --now muninn-index"
echo "     (restart it if already running:  systemctl --user restart muninn-index)"
echo "  2. Add a repo:    muninn add /path/to/repo"
echo "  3. Restart Claude Code — muninn search tools are now available"
