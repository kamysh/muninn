#!/usr/bin/env bash
# Build static binaries; optionally register the selected agent client.
set -euo pipefail
CLIENT=none
while (($#)); do
  case "$1" in
    --client) [[ $# -ge 2 ]] || { echo "--client needs codex, claude, or none" >&2; exit 2; }; CLIENT=$2; shift 2 ;;
    -h|--help) echo "Usage: ./install.sh [--client codex|claude|none] (default: none)"; exit 0 ;;
    *) echo "Unknown option: $1" >&2; exit 2 ;;
  esac
done
case "$CLIENT" in codex|claude|none) ;; *) echo "Unknown client: $CLIENT" >&2; exit 2 ;; esac
command -v nix >/dev/null || { echo "Nix is required for this source-build helper; use release downloads otherwise." >&2; exit 1; }
if [[ "$CLIENT" != none ]]; then
  command -v "$CLIENT" >/dev/null || { echo "Install $CLIENT before running --client $CLIENT." >&2; exit 1; }
fi
PROJECT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BIN_DIR="$HOME/.local/bin"
echo "Building static muninn binaries..."
OUT="$(nix build "${PROJECT_DIR}#muninn-static" --no-link --print-out-paths)"
mkdir -p "$BIN_DIR"
install -m 755 "${OUT}/bin/muninn" "${BIN_DIR}/muninn"
install -m 755 "${OUT}/bin/muninn-mcp" "${BIN_DIR}/muninn-mcp"
install -m 755 "${OUT}/bin/muninn-index" "${BIN_DIR}/muninn-index"

if [[ "$CLIENT" != none ]]; then
  if "$CLIENT" mcp get muninn >/dev/null 2>&1; then
    echo "Existing muninn registration preserved. Check its executable path with: $CLIENT mcp get muninn"
  elif [[ "$CLIENT" == codex ]]; then
    codex mcp add muninn -- "$BIN_DIR/muninn-mcp"
  else
    claude mcp add --transport stdio --scope user muninn -- "$BIN_DIR/muninn-mcp"
  fi
fi

echo "Binaries installed in $BIN_DIR."
echo "Complete database setup and client guidance using: $PROJECT_DIR/docs/get-started.md"
echo "Create and start the watcher using docs/get-started.md#5-run-the-watcher; this helper does not install a service."
