#!/usr/bin/env bash
# Export every C++ mdtest again with the pinned exporter and rewrite its
# checked-in import under mdtests/cpp-imports. Run after changing a C++
# mdtest's source or the exporter; commit the result. Needs LLVM 19.1.7.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
export CLICK_CPP_EXPORTER
CLICK_CPP_EXPORTER="$(scripts/build-cpp-exporter.sh)"
CLICK_REFRESH_CPP_IMPORTS=1 cargo nextest run --test mdtests \
    -E 'test(=cpp_mdtest_imports_match_the_pinned_exporter)'
