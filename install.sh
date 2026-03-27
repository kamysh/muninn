#!/usr/bin/env bash
# install.sh — build and register muninn with Claude Code
set -euo pipefail

INSTALL_DIR="${HOME}/.local/bin"
PROJECT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "Building release binaries (this may take a while)..."
cd "$PROJECT_DIR"
nix develop --command cargo build --release

echo "Installing to ${INSTALL_DIR}..."
mkdir -p "$INSTALL_DIR"
cp target/release/muninn-index "$INSTALL_DIR/"
cp target/release/muninn-mcp   "$INSTALL_DIR/"
cp target/release/muninn       "$INSTALL_DIR/"

echo "Registering muninn-mcp with Claude Code..."
claude mcp add muninn "${INSTALL_DIR}/muninn-mcp"

echo ""
echo "Done. Next steps:"
echo "  1. Start the indexer:  systemctl --user enable --now muninn-index"
echo "  2. Register a repo:    muninn register /path/to/repo"
echo "  3. Start Claude Code — muninn search tools are now available"
