#!/usr/bin/env bash
# Regressions for cached source-built nextest versions and binary installation.
# Use fake tools so this check never installs packages or reaches the network.
set -euo pipefail
platform="$(uname -s)"

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
if [[ "${MOCK_PRIMARY_DOWNLOAD_FAIL:-}" == 1 && "$*" == *https://get.nexte.st/* ]]; then
    exit 22
fi
if [[ "${MOCK_RELEASE_DOWNLOAD_FAIL:-}" == 1 ]]; then
    exit 22
fi
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

# A blocked shortcut can use the same pinned release on GitHub. Failure of
# both sources must still fail setup rather than accepting the stale binary.
export MOCK_PRIMARY_DOWNLOAD_FAIL=1
check_case 'cargo-nextest 0.9.142' 2
export MOCK_RELEASE_DOWNLOAD_FAIL=1
export MOCK_NEXTEST_OUTPUT='cargo-nextest 0.9.142'
cp "$directory/cached-nextest" "$directory/bin/cargo-nextest"
if "$repository/scripts/setup-environment.sh" --docs-only > "$directory/output" 2>&1; then
    echo 'error: setup accepted a stale nextest after both downloads failed' >&2
    exit 1
fi
unset MOCK_PRIMARY_DOWNLOAD_FAIL MOCK_RELEASE_DOWNLOAD_FAIL

# Refuse an incorrect downloaded version instead of silently running its tests.
export MOCK_NEXTEST_OUTPUT='cargo-nextest 0.9.142'
export MOCK_DOWNLOADED_VERSION=0.9.142
cp "$directory/cached-nextest" "$directory/bin/cargo-nextest"
if "$repository/scripts/setup-environment.sh" --docs-only > "$directory/output" 2>&1; then
    echo "error: setup accepted the wrong downloaded nextest version" >&2
    exit 1
fi

# Archive consumers need no Rust compiler or documentation-tool installation.
source "$repository/scripts/charon-toolchain.sh"
mkdir -p "$CHARON_SYSROOT/lib/rustlib/$CHARON_TARGET/lib"
touch "$CHARON_SYSROOT/lib/librustc_driver-mock.so"
mkdir -p "$CHARON_SYSROOT/bin"
cp "$directory/bin/rustup" "$CHARON_SYSROOT/bin/rustc"
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
"$repository/scripts/charon-runtime.sh" pack "$directory/runtime.tar.gz"
cached_runtime="$CHARON_SYSROOT"
export RUSTUP_HOME="$directory/cold-rustup"
source "$repository/scripts/charon-toolchain.sh"
# An ordinary test runner starts no compiler and needs no runtime; a Rust
# test runner does.
"$repository/scripts/setup-environment.sh" --test-runner >/dev/null
if "$repository/scripts/setup-environment.sh" --rust-test-runner > "$directory/output" 2>&1; then
    echo "error: setup accepted a missing Charon runtime" >&2
    exit 1
fi
"$repository/scripts/charon-runtime.sh" restore "$directory/runtime.tar.gz"
[[ -f "$CHARON_SYSROOT/lib/librustc_driver-mock.so" ]]
[[ -x "$CHARON_SYSROOT/bin/rustc" ]]
"$repository/scripts/setup-environment.sh" --rust-test-runner >/dev/null

# Libraries alone cannot satisfy Charon's pinned rustc version check.
rm "$CHARON_SYSROOT/bin/rustc"
if "$repository/scripts/setup-environment.sh" --rust-test-runner > "$directory/output" 2>&1; then
    echo "error: setup accepted a runtime without pinned rustc" >&2
    exit 1
fi
"$repository/scripts/charon-runtime.sh" restore "$directory/runtime.tar.gz"

# Refuse mismatched identities before creating the destination runtime.
printf 'wrong compiler identity\n' > "$directory/click-rust-runtime.identity"
tar -czf "$directory/wrong-runtime.tar.gz" -C "$cached_runtime" lib \
    -C "$directory" click-rust-runtime.identity
export RUSTUP_HOME="$directory/wrong-rustup"
if "$repository/scripts/charon-runtime.sh" restore "$directory/wrong-runtime.tar.gz" > "$directory/output" 2>&1; then
    echo "error: restored a mismatched Rust runtime archive" >&2
    exit 1
fi
[[ ! -e "$RUSTUP_HOME" ]]
if "$repository/scripts/charon-runtime.sh" pack "$directory/missing-runtime.tar.gz" > "$directory/output" 2>&1; then
    echo "error: packed a missing Rust runtime" >&2
    exit 1
fi
# Minimal Linux images omit docs/man pages that dpkg still lists. Keep real
# compiler files in the cache and fail if a required file is missing.
if [[ "$platform" == Linux ]]; then
    export MOCK_LLVM_FILE="$directory/libLLVM-test.so"
    export MOCK_MISSING_LLVM_FILE=""
    export MOCK_LLVM_LICENSE=""
    for license in /usr/share/doc/*/copyright; do
        if [[ -f "$license" ]]; then
            MOCK_LLVM_LICENSE="$license"
            break
        fi
    done
    printf 'compiler runtime\n' > "$MOCK_LLVM_FILE"
    cat > "$directory/bin/dpkg-query" <<'EOF'
#!/usr/bin/env bash
printf '%s\n' "$MOCK_LLVM_FILE" /usr/share/doc/clang-19/omitted-doc /usr/share/man/man1/omitted-page.1.gz
[[ -z "$MOCK_LLVM_LICENSE" ]] || printf '%s\n' "$MOCK_LLVM_LICENSE"
if [[ -n "$MOCK_MISSING_LLVM_FILE" ]]; then
    printf '%s\n' "$MOCK_MISSING_LLVM_FILE"
fi
EOF
    # Compression is orthogonal to archive membership and missing-file errors.
    cat > "$directory/bin/zstd" <<'EOF'
#!/usr/bin/env bash
exec cat
EOF
    chmod +x "$directory/bin/dpkg-query" "$directory/bin/zstd"
    "$repository/scripts/cache-llvm.sh" "$directory/llvm.tar.zst"
    members="$(tar -tf "$directory/llvm.tar.zst")"
    [[ "$members" == *"${MOCK_LLVM_FILE#/}"* ]]
    [[ "$members" != *omitted-doc* && "$members" != *omitted-page* ]]
    if [[ -n "$MOCK_LLVM_LICENSE" ]]; then
        [[ "$members" == *"${MOCK_LLVM_LICENSE#/}"* ]]
    fi
    export MOCK_MISSING_LLVM_FILE="$directory/missing-compiler.so"
    if "$repository/scripts/cache-llvm.sh" "$directory/missing.tar.zst" > "$directory/output" 2>&1; then
        echo 'error: LLVM cache accepted a missing compiler file' >&2
        exit 1
    fi
    [[ ! -e "$directory/missing.tar.zst" && ! -e "$directory/missing.tar.zst.tmp" ]]
fi
# Networks that deny apt.llvm.org use the pinned release archive: it must
# match the pinned SHA-256, extract only the toolchain subset, and never
# replace an /usr/lib/llvm-19 it did not create.
if [[ "$platform" == Linux ]]; then
    llvm_name=LLVM-19.1.7-Linux-X64
    llvm_release="$directory/llvm-release/$llvm_name"
    mkdir -p "$llvm_release/bin" "$llvm_release/include/clang" "$llvm_release/lib" "$directory/llvm-bin"
    printf 'clang\n' > "$llvm_release/bin/clang-19"
    ln -s clang-19 "$llvm_release/bin/clang"
    ln -s clang "$llvm_release/bin/clang++"
    printf '#!/usr/bin/env bash\necho 19.1.7\n' > "$llvm_release/bin/llvm-config"
    printf 'debugger\n' > "$llvm_release/bin/lldb"
    printf 'header\n' > "$llvm_release/include/clang/Basic.h"
    printf 'library\n' > "$llvm_release/lib/libclang-cpp.so.19.1"
    chmod +x "$llvm_release/bin/llvm-config"
    tar -cJf "$directory/llvm.tar.xz" -C "$directory/llvm-release" "$llvm_name"
    printf '#!/usr/bin/env bash\ncase "$1" in -s) echo Linux ;; -m) echo x86_64 ;; esac\n' \
        > "$directory/llvm-bin/uname"
    chmod +x "$directory/llvm-bin/uname"
    export MOCK_RELEASE_ARCHIVE="$directory/llvm.tar.xz"
    llvm_path="$directory/llvm-bin:$PATH"
    llvm_root="$directory/llvm-root"

    # The fake archive does not have the pinned digest.
    if PATH="$llvm_path" "$repository/scripts/install-llvm-release.sh" "$llvm_root" > "$directory/output" 2>&1; then
        echo 'error: installed an LLVM release without the pinned SHA-256' >&2
        exit 1
    fi
    [[ -z "$(ls -A "$llvm_root/opt")" && ! -e "$llvm_root/usr/lib/llvm-19" ]]

    printf '#!/usr/bin/env bash\nexit 0\n' > "$directory/llvm-bin/sha256sum"
    chmod +x "$directory/llvm-bin/sha256sum"
    PATH="$llvm_path" "$repository/scripts/install-llvm-release.sh" "$llvm_root"
    [[ "$("$llvm_root/usr/lib/llvm-19/bin/llvm-config" --version)" == 19.1.7 ]]
    [[ -L "$llvm_root/usr/lib/llvm-19/bin/clang++" ]]
    [[ -f "$llvm_root/usr/lib/llvm-19/include/clang/Basic.h" ]]
    [[ -f "$llvm_root/usr/lib/llvm-19/lib/libclang-cpp.so.19.1" ]]
    [[ ! -e "$llvm_root/opt/$llvm_name/bin/lldb" ]]
    [[ "$(ls -A "$llvm_root/opt")" == "$llvm_name" ]]
    # A second run reuses the installation without downloading.
    : > "$MOCK_DOWNLOADS"
    PATH="$llvm_path" "$repository/scripts/install-llvm-release.sh" "$llvm_root"
    [[ ! -s "$MOCK_DOWNLOADS" ]]

    other_root="$directory/other-llvm-root"
    mkdir -p "$other_root/usr/lib/llvm-19"
    if PATH="$llvm_path" "$repository/scripts/install-llvm-release.sh" "$other_root" > "$directory/output" 2>&1; then
        echo 'error: replaced an existing /usr/lib/llvm-19' >&2
        exit 1
    fi
    [[ ! -e "$other_root/opt" ]]
fi
echo "Environment setup regressions passed"
