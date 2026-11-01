#!/usr/bin/env python3
"""Exercise nightly failure aggregation with all builds and tests stubbed out."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


def executable(path, text):
    path.write_text("#!/usr/bin/env bash\nset -eu\n" + text)
    path.chmod(0o755)


with tempfile.TemporaryDirectory(prefix="click-check-nightly-") as directory:
    root = Path(directory)
    scripts = root / "scripts"
    scripts.mkdir()
    binaries = root / "bin"
    binaries.mkdir()
    (root / "src/scaling_tests").mkdir(parents=True)
    shutil.copyfile(Path(__file__).with_name("check.sh"), scripts / "check.sh")
    for name in ["test-setup-environment.sh", "mdbook-build.sh", "docs-lint.sh"]:
        executable(scripts / name, "exit 0\n")
    # The copied driver runs this regression too during quality checks.
    (scripts / "test-check-nightly.py").write_text("")
    (scripts / "proof-ratio.py").write_text("")
    for name in ["build-cpp-exporter.sh", "build-charon.sh"]:
        executable(scripts / name, 'echo /stub/frontend\n')
    for name in ["rustfmt", "cargo-nextest"]:
        executable(binaries / name, "exit 0\n")
    executable(binaries / "cargo", '''
printf '%s\\n' "$*" >> "$CHECK_TEST_LOG"
case "$1" in
    clippy) exit "$CHECK_TEST_CLIPPY" ;;
    nextest)
        if [[ " $* " == *" --no-capture "* ]]; then
            exit "$CHECK_TEST_FIXTURES"
        fi
        exit "$CHECK_TEST_UNITS" ;;
esac
''')
    for clippy, units, fixtures, expected in [
        (0, 0, 0, 0), (41, 0, 0, 41), (41, 42, 0, 42), (0, 0, 43, 43)
    ]:
        log = root / "commands.log"
        log.write_text("")
        env = dict(os.environ, PATH=f"{binaries}:{os.environ['PATH']}",
                   CHECK_TEST_LOG=str(log), CHECK_TEST_CLIPPY=str(clippy),
                   CHECK_TEST_UNITS=str(units), CHECK_TEST_FIXTURES=str(fixtures))
        result = subprocess.run(
            ["bash", str(scripts / "check.sh"), "--nightly", "--no-fail-fast"],
            env=env, capture_output=True, text=True,
        )
        assert result.returncode == expected, result.stdout + result.stderr
        runs = [line for line in log.read_text().splitlines() if line.startswith("nextest run ")]
        assert len(runs) == 2, log.read_text()
        assert "--no-capture" not in runs[0] and "--no-capture" in runs[1], runs
        assert all("--run-ignored all --profile nightly" in line for line in runs), runs
print("nightly driver: all four failure-aggregation checks passed")
