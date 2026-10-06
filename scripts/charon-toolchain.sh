# Shared compiler runtime identity for native Charon extraction.
charon_profile_path="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)/src/languages/rust/charon-profile.json"
readarray -t charon_runtime_pins < <(python3 - "$charon_profile_path" <<'PYPROFILE'
import json, sys
from pathlib import Path
profile = json.loads(Path(sys.argv[1]).read_text())
print(profile["toolchain"])
print(profile["compiler_commit"])
PYPROFILE
)
CHARON_TOOLCHAIN="${charon_runtime_pins[0]}"
CHARON_COMPILER_COMMIT="${charon_runtime_pins[1]}"
CHARON_TARGET=x86_64-unknown-linux-gnu
CHARON_SYSROOT="${RUSTUP_HOME:-$HOME/.rustup}/toolchains/$CHARON_TOOLCHAIN-$CHARON_TARGET"
CHARON_UPDATE_HASH="${RUSTUP_HOME:-$HOME/.rustup}/update-hashes/$CHARON_TOOLCHAIN-$CHARON_TARGET"
