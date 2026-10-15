#!/usr/bin/env bash
# The archive and checksum used by both release publication and its install test.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
output="${1:?usage: package-rust-frontend-archive.sh OUTPUT_DIRECTORY CHARON_BIN SYSROOT}"
charon_bin="${2:?missing Charon binary directory}"
sysroot="${3:?missing pinned sysroot}"
mkdir -p "$output"
output="$(cd "$output" && pwd -P)"
stage="$(mktemp -d "$output/.rust-frontend.XXXXXX")"
trap 'rm -rf "$stage"' EXIT
python3 scripts/package-rust-frontend.py "$stage/rust" \
    --charon-bin "$charon_bin" --sysroot "$sysroot" \
    --charon-license target/charon-source/LICENSE.md
archive=click-rust-frontend-x86_64-unknown-linux-gnu.tar.gz
tar -czf "$output/$archive" -C "$stage" rust
cd "$output"
sha256sum "$archive" > "$archive.sha256"
