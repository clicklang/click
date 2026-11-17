#!/usr/bin/env bash
# Runs the mdtest corpus under CLICK_RAISE_LOWER and summarizes how each
# fact a checked step adds, and each goal it leaves focused, round-trips
# through the canonical raiser and lowering: `same`, `polarity` (the other
# polarity of the same comparison), `differs`, `unlowered`, `unraised`, or
# `no-state` (no fixed state to raise at).
#
#   scripts/raise-lower.sh [MDTEST_FILTER] [OUTPUT]
#
# See docs/internals/spellability.md#the-raise-lower-principle. The audit
# observes only; the run's own test outcome is reported but does not decide
# the summary.
set -euo pipefail

filter="${1:-}"
output="${2:-${TMPDIR:-/tmp}/click-raise-lower.tsv}"
: > "$output"
log="$output.log"
set +e
# A set MDTEST_FILTER, even an empty one, also selects quarantined and
# nightly fixtures, so it is set only when a filter is given.
filter_env=()
[[ -n "$filter" ]] && filter_env=(MDTEST_FILTER="$filter")
env CLICK_RAISE_LOWER="$output" "${filter_env[@]}" RUST_MIN_STACK=8388608 \
    cargo nextest run --test mdtests -E 'test(=mdtests)' --no-fail-fast >"$log" 2>&1
status=$?
set -e

echo "report: $output"
echo "mdtest run exit status: $status (log: $log)"
if [[ $status -ne 0 ]]; then
    # The audit must not change a proof; a failure here is an audit defect.
    grep -E 'mdtests failed|panicked at|expected (pass|failure)' "$log" | cut -c1-300 | head -20
fi
echo "records: $(wc -l < "$output")"
echo
echo "by outcome and origin:"
awk -F'\t' '{ count[$1 "\t" $6]++ }
    END { for (key in count) printf "%7d\t%s\n", count[key], key }' "$output" | sort -rn
echo
echo "by outcome, role and kind (all but same):"
awk -F'\t' '$1 != "same" { count[$1 "\t" $2 "\t" $3]++ }
    END { for (key in count) printf "%7d\t%s\n", count[key], key }' "$output" |
    sort -rn | head -40
echo
echo "differs, examples (original | spelling | lowered):"
awk -F'\t' '$1 == "differs" { print $7 " | " $8 " | " $9 }' "$output" |
    cut -c1-300 | sort | uniq -c | sort -rn | head -20
echo
echo "unlowered, examples (original | spelling):"
awk -F'\t' '$1 == "unlowered" { print $7 " | " $8 }' "$output" |
    cut -c1-300 | sort | uniq -c | sort -rn | head -20
