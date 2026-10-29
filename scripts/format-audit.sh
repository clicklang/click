#!/usr/bin/env bash
# Runs the mdtest corpus and the example projects under CLICK_FORMAT_AUDIT
# (a debug build) and summarizes where the kernel still reads an `int32` and
# a `uint32` value, or a narrow value and its 32-bit word, as one word: by
# kind, by kind and site, and the fixtures each kind reaches.
#
#   scripts/format-audit.sh [OUTPUT]
#
# See `src/kernel/machine_integer/format_audit.rs` and
# design/machine-integers.md, "Every format its own nodes".
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

output="${1:-${TMPDIR:-/tmp}/click-format-audit.tsv}"
: > "$output"
log="$output.log"
set +e
env CLICK_FORMAT_AUDIT="$output" RUST_MIN_STACK=8388608 \
    cargo nextest run --test mdtests --test examples \
    -E 'test(=mdtests) | test(=example_projects)' --no-fail-fast >"$log" 2>&1
status=$?
set -e
echo "report: $output"
echo "corpus run exit status: $status (log: $log)"
echo "distinct uses: $(wc -l < "$output")"
python3 -I - "$output" <<'PY'
import collections, sys
by_kind = collections.defaultdict(set)
by_site = collections.Counter()
for line in open(sys.argv[1]):
    kind, site, thread, claim, tactic = (line.rstrip('\n').split('\t') + [''] * 5)[:5]
    by_kind[kind].add(thread or '<unnamed thread>')
    by_site[(kind, site)] += 1
print("\nfixtures reached, by kind:")
for kind, fixtures in sorted(by_kind.items(), key=lambda item: -len(item[1])):
    print(f"{len(fixtures):6}  {kind}")
print("\nsites, by kind (distinct uses):")
for (kind, site), count in by_site.most_common():
    print(f"{count:6}  {kind}  {site}")
PY
