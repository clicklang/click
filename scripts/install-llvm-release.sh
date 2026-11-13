#!/usr/bin/env bash
# Install the official LLVM 19.1.7 Linux x86-64 release for networks that deny
# apt.llvm.org. Only what the C++ exporter and the pinned-Clang fixtures use is
# extracted: Clang, lld (which links the release exporter), llvm-config,
# headers, and libraries (about 2.5 GiB of the release's 8.2 GiB). It goes
# under ROOT/opt, and ROOT/usr/lib/llvm-19 links to
# it, the path scripts/build-cpp-exporter.sh and tests/support/pinned_clang.rs
# look up. ROOT, the filesystem root by default, lets tests install elsewhere.
set -euo pipefail

root="${1:-}"
# The official releases this script installs, each pinned by SHA-256. macOS
# arm64 serves the C++ front end's release build (scripts/build-cpp-exporter.sh
# --release); it installs only under ROOT/opt, since /usr/lib is not writable
# there, and the build names its llvm-config with LLVM_CONFIG.
case "$(uname -s)/$(uname -m)" in
    Linux/x86_64)
        name=LLVM-19.1.7-Linux-X64
        sha256=4a5ec53951a584ed36f80240f6fbf8fdd46b4cf6c7ee87cc2d5018dc37caf679
        linkers=("bin/ld.lld")
        ;;
    Darwin/arm64)
        name=LLVM-19.1.7-macOS-ARM64
        sha256=d93bf12952d89fe4ec7501c40475718b722407da6a8d651f05c995863468e570
        linkers=("bin/ld64.lld")
        ;;
    *)
        echo "error: the LLVM 19.1.7 release fallback supports Linux x86-64 and macOS arm64 only; install LLVM 19.1.7 manually" >&2
        exit 1
        ;;
esac
url="https://github.com/llvm/llvm-project/releases/download/llvmorg-19.1.7/$name.tar.xz"
sha256_of() {
    if command -v sha256sum >/dev/null 2>&1; then
        sha256sum "$1" | cut -d' ' -f1
    else
        shasum -a 256 "$1" | cut -d' ' -f1
    fi
}

install_directory="$root/opt/$name"
link="$root/usr/lib/llvm-19"
if [[ "$(uname -s)" == Linux ]] && [[ -e "$link" || -L "$link" ]] && [[ "$(readlink "$link")" != "$install_directory" ]]; then
    echo "error: $link exists and is not a link to $install_directory; refusing to replace it" >&2
    exit 1
fi

if [[ ! -x "$install_directory/bin/llvm-config" ]]; then
    if [[ -e "$install_directory" ]]; then
        echo "error: $install_directory exists without bin/llvm-config; remove it and rerun" >&2
        exit 1
    fi
    mkdir -p "$root/opt"
    # Stage on the same filesystem so the final move is a rename.
    staging="$(mktemp -d "$root/opt/.$name.XXXXXX")"
    trap 'rm -rf "$staging"' EXIT
    curl --fail --location --silent --show-error --retry 3 "$url" \
        --output "$staging/$name.tar.xz"
    if [[ "$(sha256_of "$staging/$name.tar.xz")" != "$sha256" ]]; then
        echo "error: $url does not have the pinned SHA-256 $sha256" >&2
        exit 1
    fi
    tar -xJf "$staging/$name.tar.xz" -C "$staging" \
        "$name/bin/clang" "$name/bin/clang++" "$name/bin/clang-19" \
        "$name/bin/llvm-config" "$name/bin/lld" "${linkers[@]/#/$name/}" \
        "$name/include" "$name/lib"
    mv "$staging/$name" "$install_directory"
    rm -rf "$staging"
    trap - EXIT
fi

if [[ "$(uname -s)" == Linux ]]; then
    mkdir -p "$(dirname "$link")"
    ln -sfn "$install_directory" "$link"
fi
