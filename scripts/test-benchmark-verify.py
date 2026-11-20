#!/usr/bin/env python3
"""Exercise the benchmark command with a small stand-in for Click."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


HARNESS = Path(__file__).with_name("benchmark-verify.py").resolve()
FAKE_CLICK = """#!/usr/bin/env python3
import os
from pathlib import Path
import sys

assert sys.argv[1:7] == ["verify", "--locked", "--work-limit", "50000000",
                         "--time-limit", "10m"]
assert Path(sys.argv[7]).is_absolute()
assert os.environ["CLICK_NO_VERSION_DISPATCH"] == "1"
assert "CLICK_DISABLE_TACTIC_BUDGETS" not in os.environ
assert "CLICK_TIMING_STARTS" not in os.environ
if os.getenv("FAIL_VERIFY"):
    print("proof refused", file=sys.stderr)
    sys.exit(7)
print(os.getenv("PROOF_COUNT", "2") + " selected proofs verified")
if os.getenv("CLICK_TIMINGS") and not os.getenv("NO_COUNTERS"):
    print("click timing: operation a named operation 0.003000s 999 work", file=sys.stderr)
    work = os.getenv("TACTIC_WORK", "12")
    print("click timing: tactic sample.contract 0 step class simple statement 1 source 0"
          " 0.004000s work " + work, file=sys.stderr)
"""


class BenchmarkVerifyTests(unittest.TestCase):
    def setUp(self):
        work = tempfile.TemporaryDirectory(prefix="test-click-benchmark-")
        self.addCleanup(work.cleanup)
        self.root = Path(work.name)
        self.binary = self.root / "fake click"
        self.binary.write_text(FAKE_CLICK, encoding="utf-8")
        self.binary.chmod(0o755)
        (self.root / "proof.click").touch()
        self.report = self.root / "report"

    def invoke(self, *extra):
        return subprocess.run(
            [sys.executable, "-I", HARNESS, "--baseline", self.binary, "--output", self.report,
             "--pairs", "2", *extra, "proof.click"],
            cwd=self.root,
            env={**os.environ, "CLICK_TIMING_STARTS": "1", "CLICK_DISABLE_TACTIC_BUDGETS": "1"},
            capture_output=True,
            text=True,
            check=False,
        )

    def samples(self):
        return [
            json.loads(row)
            for row in (self.report / "samples.jsonl").read_text(encoding="utf-8").splitlines()
        ]

    def test_interleaves_quiet_samples_and_collects_work_separately(self):
        result = self.invoke("--candidate-env", "TACTIC_WORK=9")
        self.assertEqual(result.returncode, 0, result.stderr)
        samples = self.samples()
        self.assertEqual(
            [(row["phase"], row["variant"]) for row in samples],
            [("warmup", "baseline"), ("warmup", "candidate"),
             ("timed", "baseline"), ("timed", "candidate"),
             ("timed", "candidate"), ("timed", "baseline"),
             ("work", "baseline"), ("work", "candidate")],
        )
        self.assertEqual([row["completed_tactic_work"] for row in samples[-2:]], [12, 9])
        for row in samples:
            self.assertEqual(row["proof_counts"], [2])
            log = (self.report / row["log"]).read_text(encoding="utf-8")
            if row["phase"] == "timed":
                self.assertGreater(row["wall_seconds"], 0)
                self.assertGreater(row["user_seconds"] + row["system_seconds"], 0)
                self.assertNotIn("click timing:", log)
            else:
                self.assertNotIn("wall_seconds", row)
        metadata = json.loads((self.report / "metadata.json").read_text(encoding="utf-8"))
        self.assertEqual(metadata["variants"]["candidate"]["environment_overrides"], {"TACTIC_WORK": "9"})
        self.assertEqual(metadata["variants"]["baseline"]["sha256"], metadata["variants"]["candidate"]["sha256"])

    def test_failed_verification_keeps_log_and_stops_the_run(self):
        result = self.invoke("--candidate-env", "FAIL_VERIFY=1")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("verification failed", result.stderr)
        samples = self.samples()
        self.assertEqual([row["returncode"] for row in samples], [0, 7])
        self.assertIn("proof refused", (self.report / samples[-1]["log"]).read_text(encoding="utf-8"))

    def test_different_proof_counts_invalidate_a_comparison(self):
        result = self.invoke("--candidate-env", "PROOF_COUNT=1")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("selected proof counts differ", result.stderr)
        self.assertEqual(len(self.samples()), 2)

    def test_missing_work_records_fail_instead_of_reporting_zero(self):
        result = self.invoke("--candidate-env", "NO_COUNTERS=1")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("no Click timing records", result.stderr)
        self.assertNotIn("completed_tactic_work", self.samples()[-1])


if __name__ == "__main__":
    unittest.main()
