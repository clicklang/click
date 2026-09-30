#!/usr/bin/env bash
# Prepare the machine for scripts/check.sh. This is the only entry point that
# installs the Rust, test, documentation, and C++ frontend prerequisites.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

usage() {
    echo "Usage: scripts/setup-environment.sh [--docs-only]" >&2
}

docs_only=false
case "${1:-}" in
    "") ;;
    --docs-only) docs_only=true ;;
    *) usage; exit 2 ;;
esac

if ! command -v rustup >/dev/null 2>&1; then
    echo "error: rustup is required; install Rust with rustup, then rerun this script" >&2
    exit 1
fi

# rust-toolchain.toml pins the compiler and requests rustfmt and Clippy.
rustup toolchain install

nextest_version="${NEXTEST_VERSION:-0.9.143}"
nextest_output=""
if command -v cargo >/dev/null 2>&1 && cargo nextest --version >/dev/null 2>&1; then
    nextest_output="$(cargo nextest --version)"
fi
if [[ "$nextest_output" != "cargo-nextest $nextest_version "* ]]; then
    cargo install cargo-nextest --locked --version "$nextest_version" --force
fi

# The docs-only gate does not build or run the C++ importer.
if [[ "$docs_only" != true ]]; then
    needs_llvm=false
    if ! command -v llvm-config-19 >/dev/null 2>&1 || \
        [[ "$(llvm-config-19 --version)" != 19.1.7 ]]; then
        needs_llvm=true
    fi

    if [[ "$(uname -s)" == Darwin && "$needs_llvm" == true ]]; then
        echo "error: LLVM 19.1.7 development tools are required; install Homebrew llvm@19 or set LLVM_CONFIG" >&2
        exit 1
    fi

    if [[ "$(uname -s)" == Linux ]] && \
        [[ "$needs_llvm" == true || ! -x /usr/bin/gcc ]]; then
        if [[ ! -r /etc/os-release ]]; then
            echo "error: cannot identify Linux distribution for LLVM 19.1.7 setup" >&2
            exit 1
        fi
        # shellcheck disable=SC1091
        source /etc/os-release
        if [[ "${ID:-}" != ubuntu || "${VERSION_CODENAME:-}" != noble ]]; then
            echo "error: automatic LLVM setup requires Ubuntu 24.04; install LLVM 19.1.7 development packages manually" >&2
            exit 1
        fi

        apt_command=(apt-get)
        root_command=()
        if [[ "${EUID:-$(id -u)}" != 0 ]]; then
            if ! command -v sudo >/dev/null 2>&1; then
                echo "error: root or sudo access is required to install LLVM development packages" >&2
                exit 1
            fi
            apt_command=(sudo apt-get)
            root_command=(sudo)
        fi

        wget -qO- https://apt.llvm.org/llvm-snapshot.gpg.key \
            | "${root_command[@]}" tee /etc/apt/trusted.gpg.d/apt.llvm.org.asc >/dev/null
        echo "deb https://apt.llvm.org/noble/ llvm-toolchain-noble-19 main" \
            | "${root_command[@]}" tee /etc/apt/sources.list.d/llvm-19.list >/dev/null
        "${apt_command[@]}" update
        "${apt_command[@]}" install -y build-essential clang-19 libclang-19-dev llvm-19-dev libstdc++-14-dev
    fi
fi

scripts/install-tools.sh
