#!/usr/bin/env bash
# The nightly lowering audits
# (docs/internals/raise-lower-principle.md#the-raise-lower-principle): fact
# stability, whose `differs` and `paths:N` lines break an enforced rule, and
# the raise/lower round trip, whose outcomes are tracked night to night
# rather than enforced.
#
#   scripts/lowering-audits.sh [OUTPUT_DIRECTORY]
#
# Each audit runs the ordinary mdtest corpus once. The directory, by default
# `$CLICK_NIGHTLY_REPORT_DIR` or `target/lowering-audits`, receives, for
# `scripts/nightly-report.py`:
#
#   phases.tsv  `fact-stability` and `raise-lower`: seconds and the mdtest
#               run's exit status (an audit must not change a proof)
#   counts.tsv  `audit<TAB>outcome<TAB>count` for every outcome
#   fact-stability.tsv, raise-lower.tsv  the audits' own records
#
# It exits 0 when both runs complete; the report decides what fails.
set -euo pipefail

directory="${1:-${CLICK_NIGHTLY_REPORT_DIR:-target/lowering-audits}}"
mkdir -p "$directory"
export RUST_MIN_STACK="${RUST_MIN_STACK:-8388608}"
# The C++ mdtests run through the pinned exporter when it can be built.
if [[ -z "${CLICK_CPP_EXPORTER:-}" ]] && exporter="$(scripts/build-cpp-exporter.sh 2>/dev/null)"; then
    export CLICK_CPP_EXPORTER="$exporter"
fi
# Build the mdtest harness once, outside both timed runs.
cargo nextest run --test mdtests --no-run

run_audit() {
    local name="$1" script="$2" records="$directory/$1.tsv" started=$SECONDS
    "$script" "" "$records" | tee "$directory/$name.summary"
    local status
    status="$(sed -n 's/^mdtest run exit status: \([0-9]*\).*/\1/p' "$directory/$name.summary")"
    printf '%s\t%s\t%s\n' "$name" $((SECONDS - started)) "${status:-1}" >> "$directory/phases.tsv"
}

run_audit fact-stability scripts/fact-stability.sh
run_audit raise-lower scripts/raise-lower.sh

{
    # Every outcome is listed, so a zero is recorded rather than missing.
    for outcome in differs refused paths; do
        printf 'fact-stability\t%s\t%s\n' "$outcome" \
            "$(grep -c "^$outcome" "$directory/fact-stability.tsv" || true)"
    done
    for outcome in same polarity differs unlowered unraised no-state; do
        printf 'raise-lower\t%s\t%s\n' "$outcome" \
            "$(awk -F'\t' -v outcome="$outcome" '$1 == outcome' "$directory/raise-lower.tsv" | wc -l)"
    done
} > "$directory/counts.tsv"
cat "$directory/counts.tsv"
