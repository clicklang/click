#!/usr/bin/env python3
"""Exercise scripts/nightly-report.py on a small synthetic nightly."""
import json
from pathlib import Path
import subprocess
import tempfile

JUNIT = """<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="nextest-run" tests="4" failures="2">
  <testsuite name="clicklang" tests="2" failures="1">
    <testcase name="kernel::tests::passes" classname="clicklang" time="0.5"/>
    <testcase name="surface::tests::breaks" classname="clicklang" time="12.25">
      <failure message="thread 'surface::tests::breaks' panicked at src/surface/tests.rs:9:5" type="test failure">
thread 'surface::tests::breaks' panicked at src/surface/tests.rs:9:5:
assertion failed: the goal closed
note: run with `RUST_BACKTRACE=1` environment variable to display a backtrace
      </failure>
    </testcase>
  </testsuite>
  <testsuite name="clicklang::examples" tests="2" failures="2">
    <testcase name="prints_source" classname="clicklang::examples" time="2">
      <failure message="thread 'prints_source' panicked at src/surface/tests/loop_tests.rs:369:5" type="test failure">
thread 'prints_source' panicked at src/surface/tests/loop_tests.rs:369:5:
verifying "count.c";

uint64 count(uint64 n) {
      </failure>
    </testcase>
    <testcase name="debug_error" classname="clicklang::examples" time="2">
      <failure message="thread 'debug_error' panicked at tests/examples.rs:9:5" type="test failure">
thread 'debug_error' panicked at tests/examples.rs:9:5:
the rotation must recheck: ClickError { message: "`f.contract` tactic 0:\\nstep refused: a \\"borrow\\" is active", rendered: OnceLock(&lt;uninit&gt;), kind: Proof }
      </failure>
    </testcase>
  </testsuite>
  <testsuite name="clicklang::mdtests" tests="1" failures="1">
    <testcase name="mdtests" classname="clicklang::mdtests" time="700">
      <failure message="2 of 3 mdtests failed" type="test failure"/>
    </testcase>
  </testsuite>
  <testsuite name="clicklang::cpp_import" tests="1" failures="0">
    <testcase name="imports_a_span" classname="clicklang::cpp_import" time="3"/>
  </testsuite>
</testsuites>
"""


def records(*rows):
    return "".join(json.dumps(row) + "\n" for row in rows)


def mdtest(name, passed, message=None, seconds=1.0):
    return {"kind": "mdtest", "name": name, "passed": passed, "seconds": seconds, "message": message}


with tempfile.TemporaryDirectory(prefix="click-nightly-report-") as directory:
    root = Path(directory)
    nightly, audit, out = root / "nightly", root / "audit", root / "out"
    nightly.mkdir()
    audit.mkdir()
    (nightly / "mdtests.jsonl").write_text(records(
        mdtest("a.md", True, seconds=40.0),
        mdtest("reads.md", False, "expected pass, but failed: missing pure fact: defined(at(<state A>, p))"),
        mdtest("rb_next.md", False, "`/x/mdtests/rb_next.md` expected pass, but failed: `f.contract` "
               "tactic 3: fold requires the instance body facts: fact `p == 0` is not established"),
        mdtest("rb_prev.md", False, "expected pass, but failed: `g.contract` tactic 9: fold requires "
               "the instance body facts: fact `q == 0` is not established"),
    ))
    (nightly / "examples.jsonl").write_text(records(
        {"kind": "example", "name": "arena", "passed": False, "seconds": 90.0,
         "message": "sidecar `arena.click` failed:\n`requires x` proves the same obligation"},
    ))
    (nightly / "junit-tests.xml").write_text(JUNIT)
    (nightly / "phases.tsv").write_text("clippy\t60\t0\ntests\t3600\t100\nfixtures\t900\t100\n")
    (audit / "audit.jsonl").write_text(records(
        {"kind": "audit", "name": "examples/arena/cells.click:12:5", "passed": False,
         "seconds": 0, "message": "expansion did not parse"},
    ))
    jobs = root / "jobs"
    jobs.mkdir()
    (jobs / "jobs.tsv").write_text("slow-tests\tfailure\nexpansion-audit\tfailure\n")
    previous = root / "previous.json"
    previous.write_text(json.dumps({"commit": "0" * 40, "failures": [
        {"id": "mdtest:rb_next.md"},  # still failing
        {"id": "mdtest:a.md"},  # passes tonight: fixed
        {"id": "mdtest:gone.md"},  # did not run tonight
    ]}))

    result = subprocess.run(
        ["python3", "-I", str(Path(__file__).with_name("nightly-report.py")),
         "--input", str(nightly), "--input", str(audit), "--input", str(jobs),
         "--previous", str(previous), "--out", str(out), "--commit", "f" * 40,
         "--date", "2026-11-17", "--run-url", "https://example.invalid/run"],
        capture_output=True, text=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    report = json.loads((out / "report.json").read_text())
    by_id = {failure["id"]: failure for failure in report["failures"]}
    assert set(by_id) == {
        "mdtest:rb_next.md", "mdtest:rb_prev.md", "mdtest:reads.md", "example:arena",
        "audit:examples/arena/cells.click:12:5", "test:clicklang surface::tests::breaks",
        "test:clicklang::examples prints_source", "test:clicklang::examples debug_error",
    }, sorted(by_id)
    # A panic whose message is the checked Click source names its location.
    assert by_id["test:clicklang::examples prints_source"]["summary"] == (
        "panicked at src/surface/tests/loop_tests.rs:369:5; "
        "the message is the Click source it checked"), by_id["test:clicklang::examples prints_source"]
    # A debug-printed ClickError shows its message, unescaped.
    assert by_id["test:clicklang::examples debug_error"]["summary"] == (
        'the rotation must recheck: `f.contract` tactic 0: step refused: a "borrow" is active'
    ), by_id["test:clicklang::examples debug_error"]["summary"]
    # The aggregate mdtests failure is replaced by its fixtures.
    assert not any("clicklang::mdtests" in key for key in by_id)
    assert by_id["mdtest:rb_next.md"]["status"] == "persisting"
    assert by_id["mdtest:rb_prev.md"]["status"] == "new"
    assert by_id["mdtest:rb_next.md"]["summary"].startswith("expected pass, but failed:")
    assert by_id["test:clicklang surface::tests::breaks"]["summary"] == "assertion failed: the goal closed"
    assert report["fixed"] == ["mdtest:a.md"] and report["not_run"] == ["mdtest:gone.md"]
    assert by_id["mdtest:rb_prev.md"]["reproduce"] == (
        "RUST_MIN_STACK=8388608 MDTEST_FILTER=rb_prev.md cargo test --test mdtests -- --exact mdtests")
    assert by_id["test:clicklang surface::tests::breaks"]["reproduce"] == (
        "RUST_MIN_STACK=8388608 CLICK_NIGHTLY=1 cargo nextest run --run-ignored all --lib "
        "-E 'test(=surface::tests::breaks)'"), by_id["test:clicklang surface::tests::breaks"]["reproduce"]
    assert by_id["audit:examples/arena/cells.click:12:5"]["reproduce"] == (
        "cargo run --release --bin click -- audit --claim examples/arena/cells.click:12:5 "
        "examples/arena/cells.click")
    # Both fold failures share one diagnostic shape.
    assert any(set(group["ids"]) == {"mdtest:rb_next.md", "mdtest:rb_prev.md"}
               for group in report["groups"]), report["groups"]
    assert report["slowest"][0] == {"id": "example:arena", "seconds": 90.0}
    assert not any(row["id"].startswith("audit:") for row in report["slowest"])
    assert by_id["example:arena"]["summary"] == (
        "sidecar `arena.click` failed: `requires x` proves the same obligation")
    markdown = (out / "report.md").read_text()
    assert "1 new" not in markdown and "7 new, 1 persisting; 1 fixed" in markdown, markdown
    assert "## New failures" in markdown and "## Fixed since the previous night" in markdown
    assert "&lt;state A&gt;" in markdown and "<state A>" not in markdown, markdown

    # A job that failed without recording a check is reported as such.
    (jobs / "jobs.tsv").write_text("slow-tests\tsuccess\nexpansion-audit\tcancelled\n")
    empty = root / "empty"
    empty.mkdir()
    subprocess.run(
        ["python3", "-I", str(Path(__file__).with_name("nightly-report.py")),
         "--input", str(jobs), "--input", str(empty), "--out", str(out)],
        check=True, capture_output=True, text=True,
    )
    report = json.loads((out / "report.json").read_text())
    assert [f["id"] for f in report["failures"]] == ["job:expansion-audit"], report["failures"]
    assert report["failures"][0]["reproduce"] == "scripts/check.sh --audit expansion", report["failures"]

    # The lowering audits: an enforced fact-stability outcome fails, an audit
    # run whose corpus failed fails, and raise/lower counts are compared with
    # the previous night's, a rise flagged.
    lowering = root / "lowering"
    lowering.mkdir()
    (lowering / "phases.tsv").write_text("fact-stability\t600\t0\nraise-lower\t700\t100\n")
    (lowering / "counts.tsv").write_text(
        "fact-stability\tdiffers\t2\nfact-stability\trefused\t371\nfact-stability\tpaths\t0\n"
        "raise-lower\tsame\t13790\nraise-lower\tdiffers\t1210\nraise-lower\tunlowered\t360\n")
    (lowering / "fact-stability.tsv").write_text(
        "refused\tx\tA\tB\tmdtest-r\ndiffers\tx\tA\tB\tmdtest-d\n")
    (jobs / "jobs.tsv").write_text(
        "slow-tests\tsuccess\nexpansion-audit\tsuccess\n"
        "raise-lower-audit\tsuccess\nfact-stability-audit\tsuccess\n")
    previous.write_text(json.dumps({"commit": "0" * 40, "failures": [
        {"id": "lowering:fact-stability paths"},  # clean tonight: fixed
    ], "counts": [
        {"audit": "raise-lower", "outcome": "same", "count": 13780},
        {"audit": "raise-lower", "outcome": "differs", "count": 1201},
        {"audit": "raise-lower", "outcome": "unlowered", "count": 367},
    ]}))
    subprocess.run(
        ["python3", "-I", str(Path(__file__).with_name("nightly-report.py")),
         "--input", str(jobs), "--input", str(lowering), "--previous", str(previous),
         "--out", str(out), "--commit", "e" * 40],
        check=True, capture_output=True, text=True,
    )
    report = json.loads((out / "report.json").read_text())
    by_id = {failure["id"]: failure for failure in report["failures"]}
    assert set(by_id) == {"lowering:fact-stability differs", "lowering:raise-lower run"}, sorted(by_id)
    assert by_id["lowering:fact-stability differs"]["summary"] == (
        "2 `differs` lowerings; first in mdtest-d"), by_id["lowering:fact-stability differs"]
    assert by_id["lowering:fact-stability differs"]["reproduce"] == "scripts/audit.sh fact-stability"
    assert report["fixed"] == ["lowering:fact-stability paths"], report["fixed"]
    rows = {(c["audit"], c["outcome"]): c for c in report["counts"]}
    assert rows[("raise-lower", "differs")]["rose"] and not rows[("raise-lower", "same")]["rose"]
    assert not rows[("raise-lower", "unlowered")]["rose"]
    assert rows[("fact-stability", "refused")]["previous"] is None
    markdown = (out / "report.md").read_text()
    assert "**Lowering audits rose:** raise-lower `differs` 1201 → 1210" in markdown, markdown
    assert "| raise-lower | `differs` | 1210 | 1201 | **+9** (rose) |" in markdown, markdown
    assert "| raise-lower | `unlowered` | 360 | 367 | -7 |" in markdown, markdown

    # Every audit failure is in failures.tsv with a stable id and the night it
    # first failed; one new since the previous night is listed in full, and
    # failures are grouped by shape.
    import hashlib
    old_fact = ("unraised", "MemoryLoadable", "mdtests/a.md", "f.contract", "x == 1")
    new_fact = ("differs", "MemoryLoadable", "mdtests/b.md", "g.contract", "y == 2")
    (lowering / "raise-lower.failures.tsv").write_text("".join(
        "\t".join(fact + ("raised", "", f"click audit raise-lower --claim {fact[3]} {fact[2]}")) + "\n"
        for fact in (old_fact, new_fact)))
    def run_report(*extra):
        subprocess.run(
            ["python3", "-I", str(Path(__file__).with_name("nightly-report.py")),
             "--input", str(jobs), "--input", str(lowering), "--out", str(out),
             "--commit", "e" * 40, "--date", "2026-11-21", *extra],
            check=True, capture_output=True, text=True,
        )
        return json.loads((out / "report.json").read_text())
    first = run_report()
    assert first["new_audit_failures"] == [], first["new_audit_failures"]
    old_id = hashlib.sha1("\x1f".join(("raise-lower",) + old_fact[2:]).encode()).hexdigest()[:12]
    assert set(first["failure_first_seen"]) >= {old_id}, first["failure_first_seen"]
    previous.write_text(json.dumps({"commit": "0" * 40, "failures": [], "counts": [],
                                    "failure_first_seen": {old_id: "2026-11-01 000000000000"}}))
    report = run_report("--previous", str(previous))
    assert [row["container"] for row in report["new_audit_failures"]] == ["mdtests/b.md"], report
    rows = [line.split("\t") for line in (out / "failures.tsv").read_text().splitlines()]
    header, body = rows[0], rows[1:]
    assert header[0] == "id" and header[-1] == "reproduce", header
    seen = {row[header.index("container")]: row[header.index("first_seen")] for row in body}
    assert seen == {"mdtests/a.md": "2026-11-01 000000000000",
                    "mdtests/b.md": "2026-11-21 eeeeeeeeeeee"}, seen
    shape = report["shapes"][0]
    assert (shape["outcome"], shape["count"]) in {("unraised", 1), ("differs", 1)}, report["shapes"]
    markdown = (out / "report.md").read_text()
    assert "### New tonight" in markdown and "### By shape" in markdown, markdown
    assert "`click audit raise-lower --claim g.contract mdtests/b.md`" in markdown, markdown
print("nightly report: synthetic run summarized")
