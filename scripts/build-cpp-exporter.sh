#!/usr/bin/env bash
# Build the repository-owned semantic exporter against the pinned Clang API.
#
# `--check` only checks that the pinned toolchain is installed, without
# building: it exits 0 when it is, and otherwise names what is missing.
#
# `--release` builds the self-contained front end that `click add cpp`
# installs (Linux x86-64 only): Clang, LLVM and the C++ runtime are linked
# statically, and the pinned Clang's builtin headers are copied beside the
# exporter as `clang-resource/`, which it finds relative to itself. The
# output directory is the bundle; it depends only on the system C library.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

check_only=""
release=""
if [[ "${1:-}" == "--check" && -z "${2:-}" ]]; then
    check_only=1
elif [[ "${1:-}" == "--release" && -z "${2:-}" ]]; then
    release=1
elif [[ -n "${1:-}" ]]; then
    echo "usage: scripts/build-cpp-exporter.sh [--check | --release]" >&2
    exit 2
fi
host="$(uname -s)/$(uname -m)"
if [[ -n "$release" && "$host" != Linux/x86_64 && "$host" != Darwin/arm64 ]]; then
    echo "error: the release C++ front end is built on Linux x86-64 and macOS arm64 only" >&2
    exit 1
fi

# The pinned front end: one definition, read by Click and compiled in here.
profile=src/languages/cpp/frontend-profile.json
profile_field() {
    sed -n "s/^ *\"$1\": *\"\{0,1\}\([^\",]*\)\"\{0,1\},\{0,1\}\$/\1/p" "$profile"
}
expected_version="$(profile_field clang_version)"
exporter_version="$(profile_field exporter_version)"
artifact_schema="$(profile_field artifact_schema)"
if [[ -z "$expected_version" || -z "$exporter_version" || -z "$artifact_schema" ]]; then
    echo "error: $profile must name exporter_version, clang_version and artifact_schema" >&2
    exit 1
fi
if [[ -n "${LLVM_CONFIG:-}" ]]; then
    llvm_config="$LLVM_CONFIG"
elif command -v llvm-config-19 >/dev/null 2>&1; then
    llvm_config="$(command -v llvm-config-19)"
elif [[ -x /opt/homebrew/opt/llvm@19/bin/llvm-config ]]; then
    llvm_config=/opt/homebrew/opt/llvm@19/bin/llvm-config
elif [[ -x /usr/lib/llvm-19/bin/llvm-config ]]; then
    llvm_config=/usr/lib/llvm-19/bin/llvm-config
else
    echo "error: LLVM $expected_version development tools are required" >&2
    echo "Set LLVM_CONFIG to the pinned llvm-config executable." >&2
    exit 1
fi

if [[ ! -x "$llvm_config" ]]; then
    echo "error: LLVM_CONFIG names $llvm_config, which is not an executable" >&2
    exit 1
fi
actual_version="$("$llvm_config" --version)"
if [[ "$actual_version" != "$expected_version" ]]; then
    echo "error: LLVM $expected_version is required; $llvm_config reports $actual_version" >&2
    exit 1
fi

llvm_bindir="$("$llvm_config" --bindir)"
llvm_libdir="$("$llvm_config" --libdir)"
clangxx="${CLANGXX:-$llvm_bindir/clang++}"
if [[ ! -x "$clangxx" ]]; then
    echo "error: pinned clang++ not found at $clangxx" >&2
    exit 1
fi
if ! "$clangxx" --version | head -n 1 | grep -Fq "$expected_version"; then
    echo "error: $clangxx is not Clang $expected_version" >&2
    exit 1
fi

# The Clang C++ API: the shared library for a development build, or the
# static libraries the exporter uses for a release build.
clang_static_libraries=(
    Tooling ToolingCore ToolingInclusions Frontend Driver Serialization Parse
    Sema Analysis Edit AST ASTMatchers Lex Basic Rewrite Support APINotes
    Index IndexSerialization Format
)
clang_cpp=()
if [[ -n "$release" ]]; then
    for library in "${clang_static_libraries[@]}"; do
        if [[ ! -f "$llvm_libdir/libclang$library.a" ]]; then
            echo "error: the Clang $expected_version static library libclang$library.a was not found in $llvm_libdir" >&2
            exit 1
        fi
        clang_cpp+=("$llvm_libdir/libclang$library.a")
    done
    # The libraries may hold LLVM bitcode, which only the pinned lld links.
    lld="$llvm_bindir/ld.lld"
    [[ "$host" == Darwin/arm64 ]] && lld="$llvm_bindir/ld64.lld"
    if [[ ! -x "$lld" ]]; then
        echo "error: the pinned lld was not found at $lld" >&2
        exit 1
    fi
else
    for candidate in \
        "$llvm_libdir/libclang-cpp.dylib" \
        "$llvm_libdir/libclang-cpp.so.19.1" \
        "$llvm_libdir/libclang-cpp.so.19" \
        "$llvm_libdir/libclang-cpp.so"; do
        if [[ -f "$candidate" ]]; then
            clang_cpp=("$candidate")
            break
        fi
    done
    if (( ${#clang_cpp[@]} == 0 )); then
        echo "error: the Clang $expected_version C++ API library was not found in $llvm_libdir" >&2
        exit 1
    fi
fi

# Clang ships no C++ standard library on Linux: it borrows the headers of the
# newest GCC installation it finds. A distribution update that moves the
# libstdc++ runtime forward creates a newer GCC directory without its headers
# unless the matching libstdc++-N-dev package is installed, and the exporter
# build then fails deep inside a compile on `<algorithm>`. Check for that here
# and name the missing package.
if ! printf '#include <algorithm>\nint main() { return 0; }\n' \
    | "$clangxx" -std=c++20 -x c++ -fsyntax-only - >/dev/null 2>&1; then
    selected_gcc="$("$clangxx" -v -x c++ -E /dev/null 2>&1 \
        | sed -n 's/^Selected GCC installation: //p')"
    echo "error: $clangxx cannot compile a C++ program that includes <algorithm>" >&2
    if [[ -n "$selected_gcc" ]]; then
        gcc_version="${selected_gcc##*/}"
        echo "It selected the GCC installation at $selected_gcc, which has no C++ standard library headers." >&2
        echo "Install the matching headers (on Debian/Ubuntu: libstdc++-${gcc_version}-dev)," >&2
        echo "or point it at an installation that has them, for example:" >&2
        echo "  CCC_OVERRIDE_OPTIONS='+--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/<version>'" >&2
    else
        echo "Install the C++ standard library development headers for the pinned toolchain." >&2
    fi
    exit 1
fi

if [[ -n "$check_only" ]]; then
    exit 0
fi

read -r -a llvm_cxxflags <<<"$("$llvm_config" --cxxflags)"
read -r -a llvm_ldflags <<<"$("$llvm_config" --ldflags)"
read -r -a llvm_system_libs <<<"$("$llvm_config" --system-libs)"
read -r -a llvm_libs <<<"$("$llvm_config" --libs)"

# The pinned Clang's own builtin headers (`<stddef.h>`, `<stdarg.h>`, ...).
# The exporter supplies this resource directory to a command that names
# none, so a build description never has to state a machine-specific path.
resource_dir="$("$clangxx" -print-resource-dir)"
if [[ ! -f "$resource_dir/include/stddef.h" ]]; then
    echo "error: $clangxx reports resource directory $resource_dir, which has no include/stddef.h" >&2
    exit 1
fi

if [[ -n "$release" ]]; then
    default_build_directory=target/cpp-exporter-release
    # Relative to the exporter's own directory.
    compiled_resource_dir=clang-resource
    # Only the system's own libraries stay dynamic. LLVM's optional libxml2
    # is left out: nothing the exporter links uses it.
    if [[ "$host" == Darwin/arm64 ]]; then
        # macOS ships libz, libc++ and libSystem; zstd, when LLVM needs it, is
        # linked from a static archive.
        darwin_system_libs=()
        for library in "${llvm_system_libs[@]}"; do
            case "$library" in
                -lxml2) ;;
                -lzstd)
                    zstd_archive=
                    for prefix in "${ZSTD_PREFIX:-}" /opt/homebrew/opt/zstd /usr/local/opt/zstd; do
                        if [[ -n "$prefix" && -f "$prefix/lib/libzstd.a" ]]; then
                            zstd_archive="$prefix/lib/libzstd.a"
                            break
                        fi
                    done
                    if [[ -z "$zstd_archive" ]]; then
                        echo "error: LLVM needs zstd; install it (brew install zstd) or set ZSTD_PREFIX to a prefix with lib/libzstd.a" >&2
                        exit 1
                    fi
                    darwin_system_libs+=("$zstd_archive")
                    ;;
                *) darwin_system_libs+=("$library") ;;
            esac
        done
        # The release's Clang compiles against its own libc++ headers, so the
        # exporter links that release's libc++ and libc++abi statically, as
        # the Linux build links libstdc++; the system's older libc++ lacks
        # what those headers reference.
        for runtime in libc++.a libc++abi.a; do
            if [[ ! -f "$llvm_libdir/$runtime" ]]; then
                echo "error: the pinned LLVM release has no $llvm_libdir/$runtime" >&2
                exit 1
            fi
        done
        link_flags=(
            -fuse-ld=lld
            -nostdlib++
            -Wl,-dead_strip
            "${clang_cpp[@]}"
            "${llvm_libs[@]}"
            "$llvm_libdir/libc++.a"
            "$llvm_libdir/libc++abi.a"
            "${darwin_system_libs[@]}"
        )
    else
        link_flags=(
            -fuse-ld=lld
            -Wl,--gc-sections
            -Wl,--start-group "${clang_cpp[@]}" -Wl,--end-group
            "${llvm_libs[@]}"
            -Wl,-Bstatic -lz -lzstd -Wl,-Bdynamic
            -lrt -ldl -lm -lpthread
            -static-libstdc++ -static-libgcc
        )
    fi
else
    default_build_directory=target/cpp-exporter
    compiled_resource_dir="$resource_dir"
    link_flags=(
        "-Wl,-rpath,$llvm_libdir"
        "${clang_cpp[@]}"
        "${llvm_libs[@]}"
        "${llvm_system_libs[@]}"
    )
fi

build_directory="${CLICK_CPP_EXPORTER_BUILD_DIR:-$default_build_directory}"
output="$build_directory/click-cpp-exporter"
temporary="$output.tmp.$$"
mkdir -p "$build_directory"

# The build takes about 35 seconds and every gate run asks for it, so reuse
# the last binary when nothing that goes into it has changed: the exporter
# source, this script, and the toolchain and flags it resolved to.
stamp="$output.stamp"
fingerprint="$(
    {
        cat tools/cpp-exporter/* "${BASH_SOURCE[0]}" "$profile"
        "$clangxx" --version
        printf '%s\n' "$clangxx" "$resource_dir" "${CCC_OVERRIDE_OPTIONS:-}" \
            "${llvm_cxxflags[@]}" "${llvm_ldflags[@]}" "${link_flags[@]}"
    } | cksum
)"
if [[ -x "$output" && -f "$stamp" && "$(cat "$stamp")" == "$fingerprint" ]]; then
    absolute_build_directory="$(cd "$build_directory" && pwd -P)"
    printf '%s\n' "$absolute_build_directory/click-cpp-exporter"
    exit 0
fi
rm -f "$stamp"
trap 'rm -f "$temporary"' EXIT

"$clangxx" \
    "${llvm_cxxflags[@]}" \
    "-DCLICK_CLANG_RESOURCE_DIR=\"$compiled_resource_dir\"" \
    "-DCLICK_CPP_EXPORTER_VERSION=\"$exporter_version\"" \
    "-DCLICK_CPP_CLANG_VERSION=\"$expected_version\"" \
    "-DCLICK_CPP_ARTIFACT_SCHEMA=$artifact_schema" \
    -std=c++20 \
    -Wall \
    -Wextra \
    -Werror \
    -Wno-unused-parameter \
    tools/cpp-exporter/main.cpp \
    "${llvm_ldflags[@]}" \
    "${link_flags[@]}" \
    -o "$temporary"
if [[ -n "$release" ]]; then
    # Self-contained: every library the exporter loads is the system's own.
    if [[ "$host" == Darwin/arm64 ]]; then
        foreign="$(otool -L "$temporary" | tail -n +2 | awk '{print $1}' \
            | grep -vE '^(/usr/lib/|/System/Library/)' || true)"
    else
        foreign="$(ldd "$temporary" | awk '{print $1}' \
            | grep -vE '^(linux-vdso\.so|/lib64/ld-linux|libc\.so|libm\.so|libpthread\.so|libdl\.so|librt\.so)' || true)"
    fi
    if [[ -n "$foreign" ]]; then
        echo "error: the release exporter depends on libraries outside the system:" >&2
        printf '  %s\n' $foreign >&2
        exit 1
    fi
    rm -rf "$build_directory/clang-resource"
    mkdir -p "$build_directory/clang-resource"
    cp -R "$resource_dir/include" "$build_directory/clang-resource/include"
fi
mv "$temporary" "$output"
trap - EXIT
printf '%s\n' "$fingerprint" > "$stamp"

absolute_build_directory="$(cd "$build_directory" && pwd -P)"
printf '%s\n' "$absolute_build_directory/click-cpp-exporter"
