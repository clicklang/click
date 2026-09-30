#!/usr/bin/env bash
# The exporter uses rustc APIs, pinned separately from Click's stable toolchain.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
toolchain=nightly-2026-06-16
expected_commit=01dfd79246f1b2d5f146616deff08223a840a9ae
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
