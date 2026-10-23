#!/usr/bin/env bash
# Build the one cfg(test) verifier executable with the ordinary Rust compiler.
# Output is nextest's reusable binary metadata, or a CI archive when requested.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
if [[ "${1:-}" == --archive && "$#" == 2 ]]; then
    exec cargo nextest archive --lib --features fast-gate --archive-file "${2:?archive path required}"
elif [[ "$#" != 0 ]]; then
    echo "usage: scripts/fast-gate-build.sh [--archive PATH]" >&2
    exit 2
fi
exec cargo nextest list --lib --features fast-gate --list-type binaries-only --message-format json
