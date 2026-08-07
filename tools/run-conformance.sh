#!/usr/bin/env bash
set -euo pipefail

hard="$(ulimit -Hs)"
ulimit -s "$hard" 2>/dev/null || true
exec lake exe conformance "$@"
