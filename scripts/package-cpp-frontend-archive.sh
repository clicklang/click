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
case "$(uname -s)/$(uname -m)" in
    Linux/x86_64) host=x86_64-unknown-linux-gnu ;;
    Darwin/arm64) host=aarch64-apple-darwin ;;
    *) echo "error: no C++ front end is released for $(uname -s)/$(uname -m)" >&2; exit 1 ;;
esac
python3 scripts/package-cpp-frontend.py "$stage/cpp" \
    --exporter-bundle "$bundle" --llvm-license "$license" --host "$host"
archive=click-cpp-frontend-$host.tar.gz
tar -czf "$output/$archive" -C "$stage" cpp
cd "$output"
if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$archive" > "$archive.sha256"
else
    shasum -a 256 "$archive" > "$archive.sha256"
fi
