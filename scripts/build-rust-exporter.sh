#!/usr/bin/env bash
# The exporter uses rustc APIs, pinned separately from Click's stable toolchain.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
source scripts/rust-exporter-toolchain.sh
toolchain="$RUST_EXPORTER_TOOLCHAIN"
expected_commit="$RUST_EXPORTER_COMPILER_COMMIT"
actual_commit="$(rustc +"$toolchain" -vV | sed -n 's/^commit-hash: //p')"
if [[ "$actual_commit" != "$expected_commit" ]]; then
    echo "error: Rust exporter requires compiler commit $expected_commit" >&2
    exit 1
fi
sysroot="$(rustc +"$toolchain" --print sysroot)"
export CLICK_RUST_SYSROOT="$sysroot"
export RUSTFLAGS="-L native=$sysroot/lib -C link-arg=-Wl,-rpath,$sysroot/lib"
cargo +"$toolchain" build --locked --manifest-path tools/rust-exporter/Cargo.toml --target-dir target/rust-exporter >&2
printf '%s\n' "$PWD/target/rust-exporter/debug/click-rust-exporter"
