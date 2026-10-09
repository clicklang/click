#!/usr/bin/env bash
# Pinned compiler dependency for the required live Charon gate.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
# Keep this usable by the system Bash 3.2 on macOS.
{
    IFS= read -r revision
    IFS= read -r toolchain
    IFS= read -r compiler
} < <(python3 - <<'PYPROFILE'
import json
with open("src/languages/rust/charon-profile.json") as f:
    profile = json.load(f)
for key in ("extractor_revision", "toolchain", "compiler_commit"):
    print(profile[key])
PYPROFILE
)
check_only=""
if [[ "${1:-}" == "--install-toolchain" ]]; then
    rustup toolchain install "$toolchain" --profile minimal --component rustc-dev --component rust-src \
        --target x86_64-unknown-linux-gnu
elif [[ "${1:-}" == "--check" ]]; then
    # Only check that the pinned compiler is installed, without building.
    check_only=1
elif [[ -n "${1:-}" ]]; then
    echo "usage: scripts/build-charon.sh [--install-toolchain | --check]" >&2
    exit 2
fi
if [[ "$(rustc +"$toolchain" -vV 2>/dev/null | sed -n 's/^commit-hash: //p')" != "$compiler" ]]; then
    echo "error: install $toolchain with rustc-dev and rust-src for the Charon trial" >&2
    exit 1
fi
source_dir="$PWD/target/charon-source"
if [[ -n "$check_only" ]]; then
    exit 0
fi
if [[ ! -d "$source_dir" ]]; then
    git clone https://github.com/AeneasVerif/charon.git "$source_dir" >&2
fi
if [[ -n "$(git -C "$source_dir" status --porcelain)" ]]; then
    echo "error: Charon dependency checkout has local changes" >&2
    exit 1
fi
# A checkout made before the pin moved lacks the pinned revision.
if ! git -C "$source_dir" cat-file -e "$revision^{commit}" 2>/dev/null; then
    git -C "$source_dir" fetch origin >&2
fi
git -C "$source_dir" checkout --detach "$revision" >&2
sysroot="$(rustc +"$toolchain" --print sysroot)"
export LIBRARY_PATH="$sysroot/lib${LIBRARY_PATH:+:$LIBRARY_PATH}"
export CARGO_PROFILE_DEV_DEBUG=0
cargo +"$toolchain" build --locked --manifest-path "$source_dir/charon/Cargo.toml" --target-dir "$PWD/target/charon" --bin charon --bin charon-driver >&2
printf '%s\n' "$PWD/target/charon/debug/charon"
