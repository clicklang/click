#!/usr/bin/env bash
# Regressions for cached source-built nextest versions and binary installation.
# Use fake tools so this check never installs packages or reaches the network.
set -euo pipefail

repository="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
directory="$(mktemp -d)"
trap 'rm -rf "$directory"' EXIT
mkdir -p "$directory/bin" "$directory/release"

cat > "$directory/bin/rustup" <<'EOF'
#!/usr/bin/env bash
exit 0
EOF
cat > "$directory/bin/cargo" <<'EOF'
#!/usr/bin/env bash
echo "error: setup tried to compile a cached or prebuilt tool" >&2
exit 1
EOF
cat > "$directory/bin/curl" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
printf 'download\n' >> "$MOCK_DOWNLOADS"
while [[ $# -gt 0 ]]; do
    if [[ "$1" == --output ]]; then
        cp "$MOCK_RELEASE_ARCHIVE" "$2"
        exit 0
    fi
    shift
done
exit 1
EOF
cat > "$directory/cached-nextest" <<'EOF'
#!/usr/bin/env bash
printf '%s\n' "$MOCK_NEXTEST_OUTPUT"
EOF
cat > "$directory/release/cargo-nextest" <<'EOF'
#!/usr/bin/env bash
printf 'cargo-nextest %s\n' "$MOCK_DOWNLOADED_VERSION"
EOF
chmod +x "$directory/bin/"* "$directory/cached-nextest" "$directory/release/cargo-nextest"
tar -czf "$directory/nextest.tar.gz" -C "$directory/release" cargo-nextest

export CARGO_HOME="$directory"
export RUSTUP_HOME="$directory/rustup"
export MDBOOK_BIN="$directory/bin/rustup"
export PATH="$directory/bin:/usr/bin:/bin"
export NEXTEST_VERSION=0.9.143
export MOCK_RELEASE_ARCHIVE="$directory/nextest.tar.gz"
export MOCK_DOWNLOADS="$directory/downloads"
export MOCK_DOWNLOADED_VERSION=0.9.143

check_case() {
    local output="$1" expected_downloads="$2"
    export MOCK_NEXTEST_OUTPUT="$output"
    cp "$directory/cached-nextest" "$directory/bin/cargo-nextest"
    : > "$MOCK_DOWNLOADS"
    "$repository/scripts/setup-environment.sh" --docs-only >/dev/null
    [[ "$(wc -l < "$MOCK_DOWNLOADS")" -eq "$expected_downloads" ]]
}

check_case 'cargo-nextest 0.9.143' 0
check_case $'cargo-nextest 0.9.143\nrelease: 0.9.143\nhost: x86_64-unknown-linux-gnu' 0
check_case $'cargo-nextest 0.9.143 (60fa45f63 2026-08-04)\nrelease: 0.9.143' 0
check_case 'cargo-nextest 0.9.142' 1

# Refuse an incorrect downloaded version instead of silently running its tests.
export MOCK_NEXTEST_OUTPUT='cargo-nextest 0.9.142'
export MOCK_DOWNLOADED_VERSION=0.9.142
cp "$directory/cached-nextest" "$directory/bin/cargo-nextest"
if "$repository/scripts/setup-environment.sh" --docs-only > "$directory/output" 2>&1; then
    echo "error: setup accepted the wrong downloaded nextest version" >&2
    exit 1
fi

# Archive consumers need no Rust compiler or documentation-tool installation.
source "$repository/scripts/rust-exporter-toolchain.sh"
mkdir -p "$RUST_EXPORTER_SYSROOT/lib/rustlib/$RUST_EXPORTER_TARGET/lib"
touch "$RUST_EXPORTER_SYSROOT/lib/librustc_driver-mock.so"
export MOCK_NEXTEST_OUTPUT='cargo-nextest 0.9.143'
cp "$directory/cached-nextest" "$directory/bin/cargo-nextest"
cat > "$directory/bin/rustup" <<'EOF'
#!/usr/bin/env bash
echo 'error: a test runner tried to install Rust or mdBook' >&2
exit 1
EOF
cat > "$directory/bin/llvm-config-19" <<'EOF'
#!/usr/bin/env bash
echo '19.1.7'
EOF
# Use the manually provisioned platform path so this regression is independent
# of real compilers and package-manager permissions on the machine running it.
cat > "$directory/bin/uname" <<'EOF'
#!/usr/bin/env bash
echo Darwin
EOF
chmod +x "$directory/bin/llvm-config-19" "$directory/bin/uname"
"$repository/scripts/setup-environment.sh" --test-runner >/dev/null

# Fresh archive consumers have no runtime cache and still never call rustup.
"$repository/scripts/rust-exporter-runtime.sh" pack "$directory/runtime.tar.gz"
cached_runtime="$RUST_EXPORTER_SYSROOT"
export RUSTUP_HOME="$directory/cold-rustup"
source "$repository/scripts/rust-exporter-toolchain.sh"
if "$repository/scripts/setup-environment.sh" --test-runner > "$directory/output" 2>&1; then
    echo "error: setup accepted a missing exporter runtime" >&2
    exit 1
fi
"$repository/scripts/rust-exporter-runtime.sh" restore "$directory/runtime.tar.gz"
[[ -f "$RUST_EXPORTER_SYSROOT/lib/librustc_driver-mock.so" ]]
[[ ! -d "$RUST_EXPORTER_SYSROOT/bin" ]]
"$repository/scripts/setup-environment.sh" --test-runner >/dev/null

# Refuse mismatched identities before creating the destination runtime.
printf 'wrong compiler identity\n' > "$directory/click-rust-runtime.identity"
tar -czf "$directory/wrong-runtime.tar.gz" -C "$cached_runtime" lib \
    -C "$directory" click-rust-runtime.identity
export RUSTUP_HOME="$directory/wrong-rustup"
if "$repository/scripts/rust-exporter-runtime.sh" restore "$directory/wrong-runtime.tar.gz" > "$directory/output" 2>&1; then
    echo "error: restored a mismatched Rust runtime archive" >&2
    exit 1
fi
[[ ! -e "$RUSTUP_HOME" ]]
if "$repository/scripts/rust-exporter-runtime.sh" pack "$directory/missing-runtime.tar.gz" > "$directory/output" 2>&1; then
    echo "error: packed a missing Rust runtime" >&2
    exit 1
fi
echo "Environment setup regressions passed"
