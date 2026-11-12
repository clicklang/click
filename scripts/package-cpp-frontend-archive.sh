#!/usr/bin/env bash
# The archive and checksum used by both release publication and its install test.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
output="${1:?usage: package-cpp-frontend-archive.sh OUTPUT_DIRECTORY EXPORTER_BUNDLE LLVM_LICENSE}"
bundle="${2:?missing exporter bundle from scripts/build-cpp-exporter.sh --release}"
license="${3:?missing pinned LLVM license}"
mkdir -p "$output"
output="$(cd "$output" && pwd -P)"
stage="$(mktemp -d "$output/.cpp-frontend.XXXXXX")"
trap 'rm -rf "$stage"' EXIT
python3 scripts/package-cpp-frontend.py "$stage/cpp" \
    --exporter-bundle "$bundle" --llvm-license "$license"
archive=click-cpp-frontend-x86_64-unknown-linux-gnu.tar.gz
tar -czf "$output/$archive" -C "$stage" cpp
cd "$output"
sha256sum "$archive" > "$archive.sha256"
