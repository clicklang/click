#!/usr/bin/env bash
# Prepare the machine for scripts/check.sh. This is the only entry point that
# installs the Rust, test, documentation, and compiler frontend prerequisites.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

usage() {
    echo "Usage: scripts/setup-environment.sh [--docs-only|--test-runner]" >&2
}

docs_only=false
test_runner=false
case "${1:-}" in
    "") ;;
    --docs-only) docs_only=true ;;
    --test-runner) test_runner=true ;;
    *) usage; exit 2 ;;
esac

if [[ "$test_runner" != true ]] && ! command -v rustup >/dev/null 2>&1; then
    echo "error: rustup is required; install Rust with rustup, then rerun this script" >&2
    exit 1
fi

# rust-toolchain.toml pins the compiler and requests rustfmt and Clippy.
if [[ "$test_runner" != true ]]; then
    rustup toolchain install
fi

nextest_version="${NEXTEST_VERSION:-0.9.143}"
nextest_installed_version() {
    local name version rest
    # Source builds print a bare version; release builds also print a commit.
    # Compare the version token, without requiring a trailing space or commit.
    read -r name version rest <<<"$(cargo-nextest nextest --version)"
    [[ "$name" == cargo-nextest ]] && printf '%s\n' "$version"
}
if ! command -v cargo-nextest >/dev/null 2>&1 || \
    [[ "$(nextest_installed_version)" != "$nextest_version" ]]; then
    case "$(uname -s)/$(uname -m)" in
        Linux/x86_64) nextest_platform=linux ;;
        Linux/aarch64) nextest_platform=linux-arm ;;
        Darwin/*) nextest_platform=mac ;;
        *) nextest_platform= ;;
    esac
    if [[ -n "$nextest_platform" ]]; then
        nextest_directory="$(mktemp -d)"
        trap 'rm -rf "$nextest_directory"' EXIT
        curl --fail --location --silent --show-error --retry 3 \
            "https://get.nexte.st/$nextest_version/$nextest_platform" \
            --output "$nextest_directory/nextest.tar.gz"
        tar -xzf "$nextest_directory/nextest.tar.gz" -C "$nextest_directory" cargo-nextest
        cargo_bin="${CARGO_HOME:-$HOME/.cargo}/bin"
        mkdir -p "$cargo_bin"
        install -m 755 "$nextest_directory/cargo-nextest" "$cargo_bin/cargo-nextest"
        rm -rf "$nextest_directory"
        trap - EXIT
    else
        cargo install cargo-nextest --locked --version "$nextest_version" --force
    fi
    if [[ "$(nextest_installed_version)" != "$nextest_version" ]]; then
        echo "error: nextest installation did not provide version $nextest_version" >&2
        exit 1
    fi
fi

# The docs-only gate does not build or run compiler exporters.
if [[ "$docs_only" != true ]]; then
    # Charon owns compiler extraction on its separately pinned toolchain.
    # Click itself continues to use rust-toolchain.toml.
    source scripts/charon-toolchain.sh
    if [[ "$test_runner" != true ]]; then
        rustup toolchain install "$CHARON_TOOLCHAIN" --profile minimal \
            --component rustc-dev --component rust-src --target "$CHARON_TARGET"
    elif [[ ! -d "$CHARON_SYSROOT/lib/rustlib/$CHARON_TARGET/lib" ]] || \
        ! compgen -G "$CHARON_SYSROOT/lib/librustc_driver*" >/dev/null; then
        echo "error: restore the pinned Charon compiler runtime at $CHARON_SYSROOT before setting up a test runner" >&2
        exit 1
    fi
    needs_llvm=false
    if ! command -v llvm-config-19 >/dev/null 2>&1 || \
        [[ "$(llvm-config-19 --version)" != 19.1.7 ]]; then
        needs_llvm=true
    fi

    if [[ "$(uname -s)" == Darwin && "$needs_llvm" == true ]]; then
        echo "error: LLVM 19.1.7 development tools are required; install Homebrew llvm@19 or set LLVM_CONFIG" >&2
        exit 1
    fi

    needs_headers=false
    if [[ "$(uname -s)" == Linux && "$needs_llvm" != true ]] && \
        ! printf '#include <algorithm>\n' \
            | /usr/lib/llvm-19/bin/clang++ -std=c++20 -x c++ -fsyntax-only - >/dev/null 2>&1; then
        needs_headers=true
    fi

    if [[ "$(uname -s)" == Linux ]] && \
        [[ "$needs_llvm" == true || ! -x /usr/bin/gcc || "$needs_headers" == true ]]; then
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

        # Cache the pinned LLVM package files, rather than installing them on
        # every fresh CI runner. The default path also works on cloud machines.
        llvm_cache="${CLICK_LLVM_CACHE_ROOT:-${XDG_CACHE_HOME:-$HOME/.cache}/click/llvm}/19.1.7-noble-$(uname -m).tar.zst"
        if [[ -f "$llvm_cache" ]] && command -v zstd >/dev/null 2>&1; then
            "${root_command[@]}" tar --zstd -xf "$llvm_cache" -C /
            "${root_command[@]}" ldconfig
            needs_llvm=false
            if ! command -v llvm-config-19 >/dev/null 2>&1 || \
                [[ "$(llvm-config-19 --version)" != 19.1.7 ]]; then
                echo "error: cached LLVM packages do not provide LLVM 19.1.7" >&2
                exit 1
            fi
        fi

        needs_headers=false
        if ! printf '#include <algorithm>\n' \
            | /usr/lib/llvm-19/bin/clang++ -std=c++20 -x c++ -fsyntax-only - >/dev/null 2>&1; then
            needs_headers=true
        fi
        if [[ "$needs_llvm" == true || ! -x /usr/bin/gcc || "$needs_headers" == true ]]; then
            wget -qO- https://apt.llvm.org/llvm-snapshot.gpg.key \
                | "${root_command[@]}" tee /etc/apt/trusted.gpg.d/apt.llvm.org.asc >/dev/null
            echo "deb https://apt.llvm.org/noble/ llvm-toolchain-noble-19 main" \
                | "${root_command[@]}" tee /etc/apt/sources.list.d/llvm-19.list >/dev/null
            "${apt_command[@]}" update
            "${apt_command[@]}" install -y build-essential clang-19 libclang-19-dev \
                llvm-19-dev libstdc++-14-dev zstd clang-tools-19 libclang-rt-19-dev
        fi

        if [[ ! -f "$llvm_cache" ]]; then
            llvm_files="$(mktemp)"
            dpkg-query -L clang-19 libclang-19-dev llvm-19-dev libllvm19 \
                libclang-cpp19 libclang1-19 libclang-common-19-dev \
                llvm-19-linker-tools clang-tools-19 llvm-19-runtime llvm-19 \
                llvm-19-tools libclang-rt-19-dev \
                | sed 's,^/,,' | sort -u > "$llvm_files"
            mkdir -p "$(dirname "$llvm_cache")"
            # --no-recursion prevents package directory entries such as /usr
            # from accidentally including the rest of the runner filesystem.
            tar -I 'zstd -T0 -3' --no-recursion -cf "$llvm_cache.tmp" \
                -C / --verbatim-files-from --files-from "$llvm_files"
            mv "$llvm_cache.tmp" "$llvm_cache"
            rm "$llvm_files"
        fi
    fi
fi

if [[ "$test_runner" != true ]]; then
    scripts/install-tools.sh
fi
