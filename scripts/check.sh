#!/usr/bin/env bash
# The single source of truth for "is this tree green". CI runs exactly this
# script, so a local check and a CI check cannot drift apart.
#
# Judge pass/fail from this script's exit status, never from piped `cargo test`
# output. A shell pipeline reports its *last* command's status, so
# `cargo test | tail` exits 0 on a failing suite. `pipefail` below makes that
# mistake impossible inside this script.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

# Documentation-only changes have a focused gate. Keep this opt-in so the
# ordinary invocation remains the complete green-tree verdict.
if [[ "${1:-}" == "--docs-only" ]]; then
    shift
    exec scripts/check-docs.sh "$@"
fi

run_quality_checks() {
    cargo fmt --check
    scripts/test-setup-environment.sh
    cargo clippy --all-targets -- -D warnings
    scripts/mdbook-build.sh
    scripts/docs-lint.sh
}

# CI runs these checks alongside compilation, while the final required check
# still requires both this stage and every test shard to pass.
if [[ "${1:-}" == "--ci-quality" ]]; then
    run_quality_checks
    exit 0
fi

fixture_targets=(
    --test mdtests
    --test examples
    --test compiler_import
    --test cpp_import
    --test rust_import
    --test bitcoin_core_money_range
)
unit_targets=(--lib --bin click --test documentation --test condition_transport_api)

if [[ "${1:-}" == "--ci-shard" ]]; then
    artifacts="${2:?usage: scripts/check.sh --ci-shard ARTIFACTS SUITE [SHARD/TOTAL]}"
    suite="${3:?usage: scripts/check.sh --ci-shard ARTIFACTS SUITE [SHARD/TOTAL]}"
    partition="${4:-1/1}"
    nextest_args=()
    case "$suite" in
        unit)
            filter='not (binary(mdtests) | binary(examples))'
            nextest_args=(--partition "hash:$partition")
            ;;
        charon-live)
            filter='binary(rust_import) & test(charon_)'
            nextest_args=(--run-ignored only --test-threads 2 --no-fail-fast)
            ;;
        mdtests|examples)
            filter="binary($suite)"
            nextest_args=(--no-capture)
            ;;
        *) echo "error: CI suite must be unit, mdtests, examples, or charon-live" >&2; exit 2 ;;
    esac

    # A few expansion regressions recurse deeply enough to overflow the
    # default per-test thread stack on otherwise healthy runners.
    export RUST_MIN_STACK="${RUST_MIN_STACK:-8388608}"

    # All consumers reuse the exporter and Rust binaries from the build job.
    # Keep the exporter in a tar file because Actions artifacts do not retain
    # executable permissions on individual uploaded files.
    mkdir -p target/cpp-exporter
    tar -xf "$artifacts/exporter.tar" -C target/cpp-exporter
    export CLICK_CPP_EXPORTER
    CLICK_CPP_EXPORTER="$PWD/target/cpp-exporter/click-cpp-exporter"
    if [[ ! -x "$CLICK_CPP_EXPORTER" ]]; then
        echo "error: shared C++ exporter is missing at $CLICK_CPP_EXPORTER" >&2
        exit 1
    fi
    mkdir -p target/charon/debug
    tar -xf "$artifacts/charon.tar" -C target/charon/debug
    export CLICK_CHARON="$PWD/target/charon/debug/charon"
    if [[ ! -x "$CLICK_CHARON" ]]; then
        echo "error: shared Charon extractor is missing at $CLICK_CHARON" >&2
        exit 1
    fi

    # Extract at the checkout root so compile-time CARGO_BIN_EXE paths still
    # work on GitHub's identical build/test checkout paths. No Cargo build or
    # Rust toolchain is needed to run a nextest archive.
    cargo-nextest nextest run --archive-file "$artifacts/tests.tar.zst" \
        --extract-to "$PWD" --extract-overwrite \
        --filterset "$filter" "${nextest_args[@]}"
    exit 0
fi

# Explicit local counterpart of the required archive-based live CI gate.
if [[ "${1:-}" == "--charon-live" ]]; then
    export RUST_MIN_STACK="${RUST_MIN_STACK:-8388608}"
    export CLICK_CHARON="${CLICK_CHARON:-$PWD/target/charon/debug/charon}"
    scripts/build-charon.sh
    cargo nextest run --test rust_import --filterset 'test(charon_)' \
        --run-ignored only --test-threads 2 --no-fail-fast
    exit 0
fi

ci_artifacts=""
nextest_args=("$@")
if [[ "${1:-}" == "--ci-prepare" ]]; then
    ci_artifacts="${2:?usage: scripts/check.sh --ci-prepare ARTIFACTS}"
    nextest_args=()
fi

# A few expansion regressions recurse deeply enough to overflow the default
# per-test thread stack on otherwise healthy runners.
export RUST_MIN_STACK="${RUST_MIN_STACK:-8388608}"

if [[ -z "$ci_artifacts" ]]; then
    run_quality_checks
fi

# The first C++ frontend is a small repository-owned LibTooling executable.
# Build it before Rust tests so the gate fails clearly when the exact pinned
# LLVM development package is unavailable. Ordinary artifact loading does not
# execute this binary; only explicit import refresh and its focused tests do.
export CLICK_CPP_EXPORTER
CLICK_CPP_EXPORTER="$(scripts/build-cpp-exporter.sh)"

export CLICK_CHARON
CLICK_CHARON="$(scripts/build-charon.sh)"

# The gate needs nextest: `.config/nextest.toml` holds the per-test time
# budgets, and prover regressions usually manifest as hangs, which must be
# killed and named rather than waited on. Plain `cargo test` has no such
# containment, so the gate refuses to run without nextest instead of
# silently running unbounded.
if ! command -v cargo-nextest >/dev/null 2>&1; then
    echo "error: cargo-nextest not found; the gate needs its per-test time budgets" >&2
    echo "Prepare this machine with:" >&2
    echo "    scripts/setup-environment.sh" >&2
    exit 1
fi

# The combined `click` binary includes each command source file as a module.
# Cargo also discovers those source files as standalone binaries under
# `src/bin/`, so `--bins` runs their identical test bodies a second time.
# Test the shipped entry point once; clippy above still checks every target.
if [[ -n "$ci_artifacts" ]]; then
    mkdir -p "$ci_artifacts"
    cargo nextest archive "${unit_targets[@]}" "${fixture_targets[@]}" \
        --archive-file "$ci_artifacts/tests.tar.zst"
    tar -cf "$ci_artifacts/exporter.tar" \
        -C "$(dirname "$CLICK_CPP_EXPORTER")" "$(basename "$CLICK_CPP_EXPORTER")"
    tar -cf "$ci_artifacts/charon.tar" \
        -C "$(dirname "$CLICK_CHARON")" "$(basename "$CLICK_CHARON")" charon-driver
    scripts/charon-runtime.sh pack "$ci_artifacts/rust-runtime.tar.gz"
    exit 0
fi

cargo nextest run "${unit_targets[@]}" "${nextest_args[@]}"
# The fixture harnesses run one at a time, and each verifies its fixtures on
# every core. Their proof verdicts come from deterministic tactic-work
# budgets; nextest's outer timeout is process-level hang containment, not a
# proof budget. Their output is not captured: each fixture prints a line when
# it starts and when it finishes, so a stall is visible as it happens and
# named.
cargo nextest run "${fixture_targets[@]}" --test-threads 1 --no-capture "${nextest_args[@]}"
