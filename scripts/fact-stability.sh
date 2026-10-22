#!/usr/bin/env bash
# Runs the mdtest corpus under CLICK_FACT_STABILITY and summarizes the
# lowerings whose term changes when facts are available, grouped by where
# the two terms first differ.
#
#   scripts/fact-stability.sh [MDTEST_FILTER] [OUTPUT]
#
# See docs/internals/spellability.md#lowering-is-fact-stable.
set -euo pipefail

filter="${1:-}"
output="${2:-${TMPDIR:-/tmp}/click-fact-stability.tsv}"
: > "$output"
log="$output.log"
set +e
filter_env=()
[[ -n "$filter" ]] && filter_env=(MDTEST_FILTER="$filter")
env CLICK_FACT_STABILITY="$output" "${filter_env[@]}" RUST_MIN_STACK=8388608 \
    cargo nextest run --test mdtests -E 'test(=mdtests)' --no-fail-fast >"$log" 2>&1
status=$?
set -e
echo "report: $output"
echo "mdtest run exit status: $status (log: $log)"
echo "fact-dependent lowerings: $(wc -l < "$output")"
python3 -I - "$output" <<'PY'
import collections, re, sys
def tokens(text):
    return re.findall(r'[A-Za-z_][A-Za-z0-9_]*|\d+|[^\sA-Za-z0-9_]', text)
groups = collections.Counter()
for line in open(sys.argv[1]):
    fields = line.rstrip('\n').split('\t')
    if fields[0] != 'differs':
        groups[(fields[0], '', '')] += 1
        continue
    left, right = tokens(fields[2]), tokens(fields[3])
    index = 0
    while index < min(len(left), len(right)) and left[index] == right[index]:
        index += 1
    context = [t for t in left[max(0, index - 25):index] if t[:1].isupper()][-3:]
    # Variable numbers differ between runs; keep only the shape.
    shape = lambda ts: ' '.join('N' if t.isdigit() else t for t in ts[index:index + 6])
    groups[(' > '.join(context), shape(left), shape(right))] += 1
for (context, facts, fact_free), count in groups.most_common(30):
    print(f"{count:6}  {context} | with facts: {facts} | fact-free: {fact_free}")
PY
