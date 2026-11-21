#!/usr/bin/env python3
"""Propose checked replacements for written normalize calls as a Git patch."""

import argparse
import difflib
import os
from pathlib import Path
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="+", help="repository-relative files or directories")
    parser.add_argument("--click", default="click", help="Click executable built from this checkout")
    parser.add_argument("--claim", help="select one proof-unit label in one file")
    parser.add_argument("--work-limit", help="deterministic work limit per input")
    parser.add_argument("--time-limit", help="wall-clock containment limit per input")
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[1]
    tracked = subprocess.check_output(
        ["git", "ls-files", "-z", "--", *args.paths], cwd=root
    )
    files = sorted(
        path
        for path in set(map(os.fsdecode, tracked.rstrip(b"\0").split(b"\0")))
        if path.endswith(".click") or (path.startswith("mdtests/") and path.endswith(".md"))
    )
    if not files:
        parser.error("no tracked Click sidecars or Markdown mdtests matched")
    if args.claim and len(files) != 1:
        parser.error("--claim requires exactly one input file")

    command = [args.click, "expand", "--migrate-normalize"]
    for flag, value in [
        ("--claim", args.claim),
        ("--work-limit", args.work_limit),
        ("--time-limit", args.time_limit),
    ]:
        if value is not None:
            command.extend([flag, value])

    failed = False
    for path in files:
        original = (root / path).read_bytes()
        if b"normalize" not in original:
            continue
        result = subprocess.run([*command, "--", path], cwd=root, stdout=subprocess.PIPE)
        if result.returncode != 0:
            print(f"{path}: migration command failed", file=sys.stderr)
            failed = True
            continue
        for line in difflib.diff_bytes(
            difflib.unified_diff,
            original.splitlines(keepends=True),
            result.stdout.splitlines(keepends=True),
            fromfile=b"a/" + os.fsencode(path),
            tofile=b"b/" + os.fsencode(path),
        ):
            sys.stdout.buffer.write(line)
            if not line.endswith(b"\n"):
                sys.stdout.buffer.write(b"\n\\ No newline at end of file\n")
    return int(failed)


if __name__ == "__main__":
    sys.exit(main())
