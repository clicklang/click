#!/usr/bin/env bash
# Ship the compiler libraries needed by the already-built Rust exporter.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
source scripts/rust-exporter-toolchain.sh

mode="${1:?usage: rust-exporter-runtime.sh pack|restore ARCHIVE}"
archive="${2:?usage: rust-exporter-runtime.sh pack|restore ARCHIVE}"
identity="$(printf '%s\n' "$RUST_EXPORTER_TOOLCHAIN" "$RUST_EXPORTER_TARGET" "$RUST_EXPORTER_COMPILER_COMMIT")"

check_runtime() {
    if [[ ! -d "$RUST_EXPORTER_SYSROOT/lib/rustlib/$RUST_EXPORTER_TARGET/lib" ]] || \
        ! compgen -G "$RUST_EXPORTER_SYSROOT/lib/librustc_driver*" >/dev/null; then
        echo "error: pinned Rust exporter runtime libraries are missing at $RUST_EXPORTER_SYSROOT" >&2
        exit 1
    fi
}

case "$mode" in
    pack)
        check_runtime
        metadata="$(mktemp -d)"
        trap 'rm -rf "$metadata"' EXIT
        printf '%s\n' "$identity" > "$metadata/click-rust-runtime.identity"
        tar -czf "$archive" -C "$RUST_EXPORTER_SYSROOT" lib \
            -C "$metadata" click-rust-runtime.identity
        ;;
    restore)
        actual="$(tar -xOzf "$archive" click-rust-runtime.identity)"
        if [[ "$actual" != "$identity" ]]; then
            echo "error: Rust runtime archive does not match the pinned compiler, target, and toolchain" >&2
            exit 1
        fi
        mkdir -p "$RUST_EXPORTER_SYSROOT"
        tar -xzf "$archive" -C "$RUST_EXPORTER_SYSROOT" lib
        check_runtime
        ;;
    *) echo "error: expected pack or restore" >&2; exit 2 ;;
esac
