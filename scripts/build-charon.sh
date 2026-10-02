#!/usr/bin/env bash
# Optional compiler dependency for the end-to-end adapter trial.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
revision=5d6b812e5f77dbf3d7f66c21b9b57091f0e084cb
toolchain=nightly-2026-09-17
compiler=923c95cdf5ba65cea505aa2ea829f578e1506ed8
if [[ "$(rustc +"$toolchain" -vV | sed -n 's/^commit-hash: //p')" != "$compiler" ]]; then
    echo "error: install $toolchain with rustc-dev and rust-src for the Charon trial" >&2
    exit 1
fi
source_dir="$PWD/target/charon-source"
if [[ ! -d "$source_dir" ]]; then
    git clone https://github.com/AeneasVerif/charon.git "$source_dir" >&2
fi
if [[ -n "$(git -C "$source_dir" status --porcelain)" ]]; then
    echo "error: Charon dependency checkout has local changes" >&2
    exit 1
fi
git -C "$source_dir" checkout --detach "$revision" >&2
sysroot="$(rustc +"$toolchain" --print sysroot)"
export LIBRARY_PATH="$sysroot/lib${LIBRARY_PATH:+:$LIBRARY_PATH}"
export CARGO_PROFILE_DEV_DEBUG=0
cargo +"$toolchain" build --locked --manifest-path "$source_dir/charon/Cargo.toml" --target-dir "$PWD/target/charon" --bin charon --bin charon-driver >&2
printf '%s\n' "$PWD/target/charon/debug/charon"
