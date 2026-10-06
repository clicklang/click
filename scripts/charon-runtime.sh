#!/usr/bin/env bash
# Ship the pinned rustc and libraries needed by the already-built Charon.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
source scripts/charon-toolchain.sh

mode="${1:?usage: charon-runtime.sh pack|restore ARCHIVE}"
archive="${2:?usage: charon-runtime.sh pack|restore ARCHIVE}"
identity="$(printf '%s\n' "$CHARON_TOOLCHAIN" "$CHARON_TARGET" "$CHARON_COMPILER_COMMIT")"

check_runtime() {
    if [[ ! -x "$CHARON_SYSROOT/bin/rustc" ]] || \
        [[ ! -d "$CHARON_SYSROOT/lib/rustlib/$CHARON_TARGET/lib" ]] || \
        ! compgen -G "$CHARON_SYSROOT/lib/librustc_driver*" >/dev/null; then
        echo "error: pinned Charon compiler/runtime files are missing at $CHARON_SYSROOT" >&2
        exit 1
    fi
}

case "$mode" in
    pack)
        check_runtime
        metadata="$(mktemp -d)"
        trap 'rm -rf "$metadata"' EXIT
        printf '%s\n' "$identity" > "$metadata/click-rust-runtime.identity"
        tar -czf "$archive" -C "$CHARON_SYSROOT" lib bin/rustc \
            -C "$metadata" click-rust-runtime.identity
        ;;
    restore)
        actual="$(tar -xOzf "$archive" click-rust-runtime.identity)"
        if [[ "$actual" != "$identity" ]]; then
            echo "error: Rust runtime archive does not match the pinned compiler, target, and toolchain" >&2
            exit 1
        fi
        mkdir -p "$CHARON_SYSROOT"
        tar -xzf "$archive" -C "$CHARON_SYSROOT" lib bin/rustc
        check_runtime
        ;;
    *) echo "error: expected pack or restore" >&2; exit 2 ;;
esac
