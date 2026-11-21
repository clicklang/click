#!/usr/bin/env bash
# Runs Click's audits through `click audit` on a release build
# (docs/reference/cli/audit.md). Each checks a promise Click makes about every
# proof and ends with one headline: how many of the items it checked fail.
#
#   scripts/audit.sh [expansion|raise-lower|fact-stability] [PATH] [click audit options]
#
# With no audit named, all three run. PATH defaults to the repository root,
# which covers `examples/` and `mdtests/`. Records go to
# `$CLICK_NIGHTLY_REPORT_DIR` when it is set, otherwise `target/click-audit`.
# With `CLICK_NIGHTLY_REPORT_DIR`, each lowering audit also appends, for
# `scripts/nightly-report.py`:
#
#   phases.tsv  `<audit><TAB>seconds<TAB>status`, `click audit`'s status
#   counts.tsv  `<audit><TAB>outcome<TAB>count`: `failing`, `checked`,
#               `tracked`, `unexpected` and each outcome's count
#
# The exit status is `click audit`'s: only expansion failures fail it.
set -euo pipefail

kind=""
case "${1:-}" in
    expansion | raise-lower | fact-stability)
        kind="$1"
        shift
        ;;
esac
path="."
if [[ $# -gt 0 && "${1:0:1}" != "-" ]]; then
    path="$1"
    shift
fi

export RUST_MIN_STACK="${RUST_MIN_STACK:-8388608}"
# The C++ mdtests run through the pinned exporter when it can be built.
if [[ -z "${CLICK_CPP_EXPORTER:-}" ]] && exporter="$(scripts/build-cpp-exporter.sh 2>/dev/null)"; then
    export CLICK_CPP_EXPORTER="$exporter"
fi
cargo build --release --bin click

report="${CLICK_NIGHTLY_REPORT_DIR:-}"
records="${report:-target/click-audit}"
mkdir -p "$records"
started=$SECONDS
set +e
target/release/click audit ${kind:+"$kind"} --records "$records" "$@" "$path"
status=$?
set -e

if [[ -n "$report" ]]; then
    for audit in raise-lower fact-stability; do
        counts="$records/$audit.counts.tsv"
        [[ -f "$counts" ]] || continue
        printf '%s\t%s\t%s\n' "$audit" $((SECONDS - started)) "$status" >> "$report/phases.tsv"
        awk -F'\t' -v audit="$audit" '{ printf "%s\t%s\t%s\n", audit, $1, $2 }' "$counts" \
            >> "$report/counts.tsv"
    done
fi
exit "$status"
