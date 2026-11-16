#!/usr/bin/env bash
# Runs the mdtest corpus under CLICK_RAISE_LOWER_CENSUS and summarizes the
# facts and goals that do not satisfy the raise-lower principle, by kind.
#
#   scripts/raise-lower-census.sh [MDTEST_FILTER] [OUTPUT]
#
# See docs/internals/raise-lower-principle.md. The census observes only; the run's
# own test outcome is reported but does not decide the summary.
set -euo pipefail

filter="${1:-}"
output="${2:-${TMPDIR:-/tmp}/click-raise-lower-census.tsv}"
: > "$output"

log="$output.log"
set +e
# A set MDTEST_FILTER, even an empty one, also selects quarantined and
# nightly fixtures, so it is set only when a filter is given.
filter_env=()
[[ -n "$filter" ]] && filter_env=(MDTEST_FILTER="$filter")
env CLICK_RAISE_LOWER_CENSUS="$output" "${filter_env[@]}" RUST_MIN_STACK=8388608 \
    cargo nextest run --test mdtests -E 'test(=mdtests)' --no-fail-fast >"$log" 2>&1
status=$?
set -e

total=$(wc -l < "$output")
unraised=$(grep -c '^unraised' "$output" || true)
echo "census: $output"
echo "mdtest run exit status: $status (log: $log)"
if [[ $status -ne 0 ]]; then
    # The census must not change a proof; a failure here is a census defect.
    grep -E 'mdtests failed|panicked at|expected (pass|failure)' "$log" | cut -c1-300 | head -20
fi
echo "records: $total, unraised: $unraised"
echo
echo "unraised by origin:"
awk -F'\t' '{ total[$6]++ } $1 == "unraised" { count[$6]++ }
    END { for (key in total) printf "%7d of %7d\t%s\n", count[key], total[key], key }' "$output"
echo
echo "unraised by role and kind, written steps:"
awk -F'\t' '$1 == "unraised" && $6 == "written" { count[$2 "\t" $3]++ }
    END { for (key in count) printf "%7d\t%s\n", count[key], key }' "$output" |
    sort -rn
echo
echo "unraised by role and kind, all steps:"
awk -F'\t' '$1 == "unraised" { count[$2 "\t" $3]++ }
    END { for (key in count) printf "%7d\t%s\n", count[key], key }' "$output" |
    sort -rn
echo
echo "raised by role and kind:"
awk -F'\t' '$1 == "raised" { count[$2 "\t" $3]++ }
    END { for (key in count) printf "%7d\t%s\n", count[key], key }' "$output" |
    sort -rn | head -20
