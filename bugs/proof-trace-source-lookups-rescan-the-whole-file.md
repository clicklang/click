# Proof trace source lookups repeatedly scan the whole file

## Reproduced defect

Rendering an existing checked proof trace repeatedly tokenizes and scans the
entire source container to locate individual written tactics. This violates
the verification efficiency contract's approximately linear selected-source
and explicit-proof requirement. Trace text is diagnostic; generating line and
column labels should not dominate checking the proof.

The CLI caches some resolved structural paths and outer declaration positions,
but each new nested path, same-line ambiguity query, or have-body containment
query still invokes a whole-file scan. The relevant paths are
`ProofSourceLocations::position` and `proof_error_report` in
`src/bin/click-verify.rs`, and `nested_tactic_source_position`,
`tactic_starts_on_line`, `tactic_line_has_multiple_starts`, and
`tactic_have_body_contains_position` in `src/surface/expansion.rs`.
`tactic_starts_on_line` visits all proof blocks in the container even when only
one line is queried. Existing per-path caching does not amortize the source
index construction across distinct steps.

## Small reproduction

Run against an unoptimized CLI, using the path to the built `click` binary:

```python
from pathlib import Path
import subprocess
import tempfile
import time

cli = "/path/to/target/debug/click"
with tempfile.TemporaryDirectory() as directory:
    root = Path(directory)
    (root / "empty.c").write_text("int anchor(void) { return 0; }\n")
    for count in (100, 200, 400):
        proof = root / f"proof-{count}.click"
        proof.write_text(
            'verifying "empty.c";\ntheorem many_haves() {\n'
            ' ensures 0 == 0 by {\n'
            + '  have 0 == 0 by { normalize(); }\n' * count
            + '  normalize();\n }\n}\n'
        )
        for traced in (False, True):
            command = [cli, "verify"]
            if traced:
                command += ["--trace-proof", "many_haves"]
            command.append(str(proof))
            started = time.monotonic()
            result = subprocess.run(command, capture_output=True, timeout=60)
            assert result.returncode == 0, result.stderr.decode()
            print(count, traced, time.monotonic() - started)
```

Observed ordinary/trace times in seconds: 100 steps 0.213/0.228;
200 steps 0.110/0.601; 400 steps 0.157/1.772. All six checks passed. These
wall times locate the cost; they are not proposed regression thresholds.
The source and emitted trace both grow approximately linearly, while the
rendering work repeatedly scans the growing file for its growing set of sites.

An isolated call to `tactic_line_has_multiple_starts` on the assembled Adler
source (461,702 bytes) takes about 0.2 seconds: 10 queries took 1.960 seconds,
and 50 took 9.671 seconds. The original failed trace emitted 1,989 tactic
headings at 690 distinct line/column locations, approximately 347 KB of text.

## End-to-end timing

The scalar-tail checksum investigation's ordinary targeted verification took
129.425 seconds, including 125.971 seconds of user CPU. Source resolution and
frontend/environment setup took roughly three seconds. It checked 1,118 timed
tactic actions, including 697 haves, 167 applications, 112 explicit steps,
and 59 execute-until requests. This is symbolic proof work, not iteration over
22,207 concrete input bytes. An exclusive tactic-time breakdown attributes
about 40 seconds to nested have scope handling, 36 seconds to execute-until,
and 15 seconds to automatic have steps. More profiling is needed before
classifying ordinary verification's cost as a defect.

In a timed trace of the same failed contract, verifier-core finished in
115.772 seconds (about 120 seconds after process launch); source location
resolution then began and the process continued using one CPU to render the
report. The timed run finished after 587.894 seconds (564.853 seconds of
user CPU). Its first report line arrived after 586.520 seconds: roughly 466
seconds after verifier-core finished, including about four seconds of source
resolution. Emitting the report and finishing took another 1.375 seconds.
Thus the avoidable delay is report construction, not writing a 347 KB trace.
The earlier complete untimed trace also took roughly ten minutes. The repeated
lookup microbenchmark identifies a concrete source-indexing defect; it does
not attribute every second of report construction to one helper.
This separates trace presentation cost from proof checking and output byte count.
No source program, proof claim, artifact, or verifier limit was changed for
the comparison. The only added diagnostics were existing CLICK_TIMINGS and
CLICK_TIMING_STARTS events.

## Acceptance

- Tokenize/index each immutable source container once per report, sharing
  source-path, line-start, sibling-tactic, and containment information across
  queries. Do not merely cache each distinct query after its first full scan.
- Add deterministic scaling coverage over source size, number of traced sites,
  and unrelated source. Source-index construction plus report lookup work
  should scale with source size plus selected sites and emitted content,
  without a per-site whole-file scan.
- Preserve existing trace facts, source locations, nested have/branch selection,
  same-line columns, UTF-8 locations, and long output. No truncation, step cap,
  reduced verification, altered proof, or raised limit is a remedy.
- Recheck the complete original Adler trace and the small reproduction, and
  attribute checking and rendering separately. An optimized binary alone is
  not a fix for the repeated-source-scan complexity.
