#!/usr/bin/env python3
"""How many hand-written `have` statements the proofs no longer need.

    evals/auto.py [--jobs N] [--per-file N] [--only SUBSTRING]
                  [--out results.jsonl] [--write-baseline]

The corpus is every `.click` sidecar of the projects listed in
`evals/auto/corpus.txt`. A site is a `have P ...;` statement whose `have` line
holds the whole proposition: a one-line `have` or one with a `by { ... }`
block. The eval deletes the whole statement in a scratch copy of the project
and asks whether the proof unit that contained it still verifies. A deletable
`have` states a fact the proof's own automation (`auto` at the claims, `simp`,
the steps after it) already finds, so the proof can be that much shorter.

`click verify FILE:LINE:COLUMN` checks only the proof unit that contains the
site. The verdict is the exit status. For a failure, the first line naming a
reason is kept as a label for reading, never as the verdict.

Each file contributes at most `--per-file` sites (default 20), chosen with a
fixed seed so the sample is the same on every run. Results are compared with
`evals/auto/baseline.json`; `--write-baseline` replaces it. A file whose
unmodified sidecar does not verify is reported and skipped.

Uses the optimized verifier at `$CARGO_TARGET_DIR/profiling/click` (built here
unless `CLICK` names another binary). Sites run in parallel; verdicts do not
depend on load, because every tactic budget is deterministic work, and the
time limit is only crash containment.
"""

import argparse
import concurrent.futures
import json
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
EVAL_DIR = os.path.join(ROOT, "evals", "auto")
CORPUS = os.path.join(EVAL_DIR, "corpus.txt")
BASELINE = os.path.join(EVAL_DIR, "baseline.json")
SITE_TIME_LIMIT = "5m"
# The unmodified sidecar is verified whole, and the largest take minutes.
FILE_TIME_LIMIT = "30m"
HAVE = re.compile(r"^(\s*)have (.+?)( by \{| by [a-z_]+(\(.*\))?;\s*$|;\s*$)")
REASONS = [
    ("budget", "exhausted"),
    ("timeout", "time limit"),
    ("syntax", "syntax error"),
]


def verifier():
    if os.environ.get("CLICK"):
        return os.environ["CLICK"]
    target = os.environ.get("CARGO_TARGET_DIR", os.path.join(ROOT, "target"))
    subprocess.run(
        ["cargo", "build", "--profile", "profiling", "--bin", "click"], cwd=ROOT, check=True
    )
    return os.path.join(target, "profiling", "click")


def corpus_projects():
    projects = []
    with open(CORPUS) as corpus:
        for line in corpus:
            line = line.split("#", 1)[0].strip()
            if line:
                projects.append(line)
    return projects


def proof_end(text, open_brace):
    """The index just past the `}` matching `text[open_brace]`, skipping
    `#` comments."""
    depth = 0
    index = open_brace
    while index < len(text):
        character = text[index]
        if character == "#":
            newline = text.find("\n", index)
            index = len(text) if newline < 0 else newline
            continue
        if character == "{":
            depth += 1
        elif character == "}":
            depth -= 1
            if depth == 0:
                return index + 1
        index += 1
    return None


def sites(path):
    """Each `have` statement whose proposition is on the `have` line and has
    no braces of its own, as (line, column, proposition, start, end), where
    `text[start:end]` is the whole statement with its line ending."""
    with open(path) as source:
        text = source.read()
    found = []
    offset = 0
    for number, line in enumerate(text.split("\n"), start=1):
        match = HAVE.match(line)
        proposition = match.group(2) if match else ""
        if match and "{" not in proposition and "}" not in proposition:
            if match.group(3) == " by {":
                end = proof_end(text, offset + match.end() - 1)
            else:
                end = offset + len(line)
            if end is not None:
                newline = text.find("\n", end)
                end = len(text) if newline < 0 else newline + 1
                found.append((number, len(match.group(1)) + 1, proposition, offset, end))
        offset += len(line) + 1
    return text, found


def site_key(relative, proposition, occurrence):
    """A key that survives edits elsewhere in the file: the file, the written
    proposition, and which occurrence of it this is."""
    return f"{relative}::{proposition}::{occurrence}"


def label(output):
    for line in output.splitlines():
        lowered = line.lower()
        for reason, needle in REASONS:
            if needle in lowered:
                return reason
    return "failed"


def run_unit(click, path, line, column):
    start = time.monotonic()
    completed = subprocess.run(
        [click, "verify", "--time-limit", SITE_TIME_LIMIT, f"{path}:{line}:{column}"],
        capture_output=True,
        text=True,
    )
    elapsed = time.monotonic() - start
    return completed.returncode, completed.stdout + completed.stderr, elapsed


def evaluate_file(click, project, relative, chosen):
    """Verifies `relative` unmodified, then with each chosen site deleted,
    in a private copy of the examples."""
    results = []
    with tempfile.TemporaryDirectory(prefix="click-auto-eval-") as scratch:
        # Copy every example, not only this project: a sidecar may import
        # another project's declarations by a relative path.
        shutil.copytree(os.path.join(ROOT, "examples"), os.path.join(scratch, "examples"))
        path = os.path.join(scratch, relative)
        text, _ = sites(path)
        completed = subprocess.run(
            [click, "verify", "--time-limit", FILE_TIME_LIMIT, path],
            capture_output=True,
            text=True,
        )
        if completed.returncode != 0:
            return [{"file": relative, "skipped": "unmodified sidecar does not verify"}]
        for key, (line, column, proposition, by, end) in chosen:
            edited = text[:by] + text[end:]
            with open(path, "w") as source:
                source.write(edited)
            # The line before the deleted statement is still inside its proof
            # unit; the statement's own line may now be the unit's last brace.
            above = edited.split("\n")[line - 2]
            target_column = len(above) - len(above.lstrip()) + 1
            status, output, elapsed = run_unit(click, path, line - 1, target_column)
            results.append(
                {
                    "key": key,
                    "file": relative,
                    "line": line,
                    "proposition": proposition,
                    "deletable": status == 0,
                    "reason": None if status == 0 else label(output),
                    "seconds": round(elapsed, 2),
                }
            )
        with open(path, "w") as source:
            source.write(text)
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--jobs", type=int, default=os.cpu_count() or 1)
    parser.add_argument("--per-file", type=int, default=20)
    parser.add_argument("--only", help="evaluate only files whose path contains this")
    parser.add_argument("--out", help="write one JSON line per site here")
    parser.add_argument("--write-baseline", action="store_true")
    arguments = parser.parse_args()

    click = verifier()
    work = []
    for project in corpus_projects():
        for directory, _, files in os.walk(os.path.join(ROOT, project)):
            for name in sorted(files):
                if not name.endswith(".click"):
                    continue
                relative = os.path.relpath(os.path.join(directory, name), ROOT)
                if arguments.only and arguments.only not in relative:
                    continue
                _, found = sites(os.path.join(ROOT, relative))
                seen = {}
                keyed = []
                for site in found:
                    occurrence = seen.get(site[2], 0)
                    seen[site[2]] = occurrence + 1
                    keyed.append((site_key(relative, site[2], occurrence), site))
                chosen = random.Random(relative).sample(
                    keyed, min(arguments.per_file, len(keyed))
                )
                chosen.sort(key=lambda item: item[1][0])
                if chosen:
                    work.append((project, relative, chosen))

    started = time.monotonic()
    results = []
    with concurrent.futures.ThreadPoolExecutor(arguments.jobs) as pool:
        futures = [
            pool.submit(evaluate_file, click, project, relative, chosen)
            for project, relative, chosen in work
        ]
        for future in concurrent.futures.as_completed(futures):
            results.extend(future.result())
    elapsed = time.monotonic() - started

    skipped = [result for result in results if "skipped" in result]
    measured = sorted(
        (result for result in results if "skipped" not in result), key=lambda r: r["key"]
    )
    deletable = [result for result in measured if result["deletable"]]
    reasons = {}
    for result in measured:
        if not result["deletable"]:
            reasons[result["reason"]] = reasons.get(result["reason"], 0) + 1
    times = sorted(result["seconds"] for result in measured)

    files = len({result["file"] for result in measured})
    print(f"have-deletion eval: {files} files, {len(measured)} sites, {elapsed / 60:.0f}m")
    if measured:
        share = 100 * len(deletable) / len(measured)
        print(f"deletable {len(deletable):5} / {len(measured)}  {share:.1f}%")
        print(f"needed    {len(measured) - len(deletable):5}")
        for reason, count in sorted(reasons.items(), key=lambda item: -item[1]):
            print(f"  {reason:<12} {count}")
        print(
            f"seconds per site  median {times[len(times) // 2]:.1f}, "
            f"p95 {times[min(len(times) - 1, len(times) * 95 // 100)]:.1f}"
        )
    for result in skipped:
        print(f"skipped  {result['file']}: {result['skipped']}")

    current = {result["key"]: result["deletable"] for result in measured}
    if os.path.exists(BASELINE):
        with open(BASELINE) as source:
            baseline = json.load(source)
        gained = sorted(key for key, ok in current.items() if ok and baseline.get(key) is False)
        lost = sorted(key for key, ok in current.items() if not ok and baseline.get(key) is True)
        new = sorted(key for key in current if key not in baseline)
        print(f"vs baseline  +{len(gained)} deletable, -{len(lost)} lost, {len(new)} new sites")
        for key in lost:
            print(f"  lost   {key}")
        for key in gained:
            print(f"  gained {key}")
    if arguments.write_baseline:
        with open(BASELINE, "w") as target:
            json.dump(current, target, indent=1, sort_keys=True)
            target.write("\n")
        print(f"wrote {os.path.relpath(BASELINE, ROOT)}")
    if arguments.out:
        with open(arguments.out, "w") as target:
            for result in measured:
                target.write(json.dumps(result) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
