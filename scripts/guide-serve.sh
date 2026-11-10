#!/usr/bin/env bash
# Serve the human-written guide in guide/ as a live-reloading local site.
# The site's configuration is in site/. Arguments go to `vitepress dev`,
# such as `--port 4000` or `--open`.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/../site"

if ! command -v npm >/dev/null; then
    echo "guide-serve: npm is required; install Node.js 18 or later" >&2
    exit 1
fi

if [[ ! -d node_modules || package-lock.json -nt node_modules ]]; then
    npm ci
fi

exec npx vitepress dev "$@"
