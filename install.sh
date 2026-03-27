#!/usr/bin/env bash
# install.sh — build and register ai-mem with Claude Code
set -euo pipefail

INSTALL_DIR="${HOME}/.local/bin"
PROJECT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "Building release binaries (this may take a while)..."
cd "$PROJECT_DIR"
nix develop --command cargo build --release

echo "Installing to ${INSTALL_DIR}..."
mkdir -p "$INSTALL_DIR"
cp target/release/ai-mem-index "$INSTALL_DIR/"
cp target/release/ai-mem-mcp   "$INSTALL_DIR/"
cp target/release/ai-mem       "$INSTALL_DIR/"

echo "Registering ai-mem-mcp with Claude Code..."
claude mcp add ai-mem "${INSTALL_DIR}/ai-mem-mcp"

echo ""
echo "Done. Next steps:"
echo "  1. Start the indexer:  systemctl --user enable --now ai-mem-index"
echo "  2. Register a repo:    ai-mem register /path/to/repo"
echo "  3. Start Claude Code — ai-mem search tools are now available"