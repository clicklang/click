#!/usr/bin/env bash
# Cache installed LLVM files, tolerating manuals omitted by minimal images.
set -euo pipefail

llvm_cache="${1:?usage: scripts/cache-llvm.sh ARCHIVE}"
llvm_files="$(mktemp)"
trap 'rm -f "$llvm_files" "$llvm_cache.tmp"' EXIT
dpkg-query -L clang-19 libclang-19-dev llvm-19-dev libllvm19 \
    libclang-cpp19 libclang1-19 libclang-common-19-dev \
    llvm-19-linker-tools clang-tools-19 llvm-19-runtime llvm-19 \
    llvm-19-tools libclang-rt-19-dev \
    | while IFS= read -r path; do
        case "$path" in
            /usr/share/doc|/usr/share/doc/*|/usr/share/man|/usr/share/man/*)
                [[ -e "$path" || -L "$path" ]] || continue ;;
        esac
        printf '%s\n' "${path#/}"
    done | sort -u > "$llvm_files"
mkdir -p "$(dirname "$llvm_cache")"
# Keep installed documentation and license files. Required compiler files must
# still exist: tar fails if any non-documentation entry is missing.
# --no-recursion prevents directory entries from including unrelated files.
tar -I 'zstd -T0 -3' --no-recursion -cf "$llvm_cache.tmp" \
    -C / --verbatim-files-from --files-from "$llvm_files"
mv "$llvm_cache.tmp" "$llvm_cache"
