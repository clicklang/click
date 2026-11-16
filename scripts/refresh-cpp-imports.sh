#!/usr/bin/env bash
# Export C++ mdtests and committed project fixtures again with the pinned
# exporter. Run after changing their source or the exporter; commit the result.
# Needs LLVM 19.1.7.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
export CLICK_CPP_EXPORTER
CLICK_CPP_EXPORTER="$(scripts/build-cpp-exporter.sh)"
CLICK_REFRESH_CPP_IMPORTS=1 cargo nextest run --test mdtests \
    -E 'test(=cpp_mdtest_imports_match_the_pinned_exporter)'

CLICK_REFRESH_CPP_IMPORTS=1 cargo nextest run --test cpp_import \
    --run-ignored only -E 'test(=committed_cpp_project_imports_match_the_pinned_exporter)'
