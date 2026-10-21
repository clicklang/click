#!/usr/bin/env bash
# Runs the mdtest corpus under CLICK_SPELLABILITY_CENSUS and summarizes the
# facts and goals the premise speller could not spell, by kind.
#
#   scripts/spellability-census.sh [MDTEST_FILTER] [OUTPUT]
#
# See docs/internals/spellability.md. The census observes only; the run's
# own test outcome is reported but does not decide the summary.
set -euo pipefail

filter="${1:-}"
output="${2:-${TMPDIR:-/tmp}/click-spellability-census.tsv}"
: > "$output"

log="$output.log"
set +e
# A set MDTEST_FILTER, even an empty one, also selects quarantined and
# nightly fixtures, so it is set only when a filter is given.
filter_env=()
[[ -n "$filter" ]] && filter_env=(MDTEST_FILTER="$filter")
env CLICK_SPELLABILITY_CENSUS="$output" "${filter_env[@]}" RUST_MIN_STACK=8388608 \
    cargo nextest run --test mdtests -E 'test(=mdtests)' --no-fail-fast >"$log" 2>&1
status=$?
set -e

total=$(wc -l < "$output")
unspelled=$(grep -c '^unspelled' "$output" || true)
echo "census: $output"
echo "mdtest run exit status: $status (log: $log)"
if [[ $status -ne 0 ]]; then
    # The census must not change a proof; a failure here is a census defect.
    grep -E 'mdtests failed|panicked at|expected (pass|failure)' "$log" | cut -c1-300 | head -20
fi
echo "records: $total, unspelled: $unspelled"
echo
echo "unspelled by role and kind:"
awk -F'\t' '$1 == "unspelled" { count[$2 "\t" $3]++ }
    END { for (key in count) printf "%7d\t%s\n", count[key], key }' "$output" |
    sort -rn
echo
echo "spelled by role and kind:"
awk -F'\t' '$1 == "spelled" { count[$2 "\t" $3]++ }
    END { for (key in count) printf "%7d\t%s\n", count[key], key }' "$output" |
    sort -rn | head -20
