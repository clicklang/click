#!/usr/bin/env bash
# Transfer the prepare job's pinned runtime to cache-miss archive consumers.
set -euo pipefail

repository="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
source "$repository/scripts/rust-exporter-toolchain.sh"

runtime_ready() {
    [[ -d "$RUST_EXPORTER_SYSROOT/lib/rustlib/$RUST_EXPORTER_TARGET/lib" ]] &&
        compgen -G "$RUST_EXPORTER_SYSROOT/lib/librustc_driver*" >/dev/null
}

if [[ $# != 2 ]]; then
    echo "Usage: scripts/rust-exporter-runtime-archive.sh pack|restore ARCHIVE" >&2
    exit 2
fi
case "$1" in
    pack)
        if ! runtime_ready; then
            echo "error: pinned Rust exporter runtime is incomplete at $RUST_EXPORTER_SYSROOT" >&2
            exit 1
        fi
        tar -czf "$2" -C "$RUST_EXPORTER_SYSROOT" .
        ;;
    restore)
        mkdir -p "$RUST_EXPORTER_SYSROOT"
        tar -xzf "$2" -C "$RUST_EXPORTER_SYSROOT"
        if ! runtime_ready; then
            echo "error: runtime archive did not provide the pinned Rust exporter runtime" >&2
            exit 1
        fi
        ;;
    *)
        echo "error: expected pack or restore" >&2
        exit 2
        ;;
esac
