#!/usr/bin/env bash
# Focused gate for prose and documentation metadata changes.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

# Docs still need to render and pass the source-backed documentation checks.
# They do not need the compiler, Clippy, or the verifier/unit-test suites.
scripts/mdbook-build.sh
scripts/docs-lint.sh

if ! command -v cargo-nextest >/dev/null 2>&1; then
    echo "error: cargo-nextest not found; the documentation gate uses its test containment" >&2
    echo "Prepare this machine with:" >&2
    echo "    scripts/setup-environment.sh --docs-only" >&2
    exit 1
fi

cargo nextest run --test documentation "$@"
