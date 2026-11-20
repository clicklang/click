#!/usr/bin/env python3
"""Compare end-to-end verification with interleaved runs of two Click variants."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import resource
import statistics
import subprocess
import tempfile
import time


DEFAULT_TARGETS = ("examples/arena", "examples/owned-vector", "examples/rust-iterators")
CONTROLS = (
    "CLICK_DISABLE_TACTIC_BUDGETS",
    "CLICK_NO_VERSION_DISPATCH",
    "CLICK_TIMINGS",
    "CLICK_TIMING_STARTS",
)
PROOFS = re.compile(r"^(\d+) selected proofs? verified$")
TACTIC_WORK = re.compile(r"^click timing: tactic .* \d+\.\d+s work (\d+)$")


def parse_overrides(items):
    overrides = {}
    for item in items:
        name, separator, value = item.partition("=")
        if not separator or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", name):
            raise ValueError(f"expected an environment override NAME=VALUE, got {item!r}")
        if name in CONTROLS:
            raise ValueError(f"{name} is controlled by the benchmark")
        if name in overrides:
            raise ValueError(f"duplicate environment override {name}")
        overrides[name] = value
    return overrides


def executable(value):
    path = Path(value).expanduser().resolve(strict=True)
    if not path.is_file() or not os.access(path, os.X_OK):
        raise ValueError(f"expected an executable Click binary at {path}")
    return path


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as reader:
        for block in iter(lambda: reader.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def summarize_log(log, measure_work):
    proofs = []
    tactic_work = 0
    saw_timing = False
    with log.open(encoding="utf-8", errors="replace") as reader:
        for line in reader:
            line = line.rstrip("\r\n")
            if match := PROOFS.fullmatch(line):
                proofs.append(int(match[1]))
            if measure_work and line.startswith("click timing: "):
                saw_timing = True
                if match := TACTIC_WORK.fullmatch(line):
                    tactic_work += int(match[1])
                elif line.startswith("click timing: tactic ") and " work " in line:
                    raise ValueError(f"unsupported tactic work record in {log}: {line!r}")
    if sum(proofs) == 0:
        raise ValueError(f"no verified proofs were reported in {log}")
    if measure_work and not saw_timing:
        raise ValueError(f"no Click timing records in {log}")
    return proofs, tactic_work


def workload_checkout():
    try:
        revision = subprocess.run(
            ["git", "rev-parse", "HEAD"], capture_output=True, text=True, check=False
        )
    except FileNotFoundError:
        return None
    if revision.returncode:
        return None
    status = subprocess.run(
        ["git", "status", "--porcelain", "--untracked-files=no"],
        capture_output=True, text=True, check=False,
    )
    return {
        "revision": revision.stdout.strip(),
        "tracked_changes": bool(status.stdout) if status.returncode == 0 else None,
    }


def run(target, variant, phase, round_number, binary, environment, limits, log, samples):
    measure_work = phase == "work"
    if measure_work:
        environment = {**environment, "CLICK_TIMINGS": "1"}
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start = time.monotonic()
    with log.open("wb") as output:
        completed = subprocess.run(
            [str(binary), "verify", "--locked", *limits, str(target)],
            env=environment,
            stdout=output,
            stderr=subprocess.STDOUT,
            check=False,
        )
    wall_seconds = time.monotonic() - start
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    sample = {
        "target": str(target),
        "variant": variant,
        "phase": phase,
        "round": round_number,
        "returncode": completed.returncode,
        "log": log.name,
    }
    if phase == "timed":
        sample.update(
            wall_seconds=wall_seconds,
            user_seconds=after.ru_utime - before.ru_utime,
            system_seconds=after.ru_stime - before.ru_stime,
        )
    try:
        if completed.returncode:
            raise ValueError(f"{variant} verification failed on {target} (exit {completed.returncode}). See {log}")
        proofs, work = summarize_log(log, measure_work)
        sample["proof_counts"] = proofs
        if measure_work:
            sample["completed_tactic_work"] = work
        return sample
    finally:
        samples.write(json.dumps(sample) + "\n")
        samples.flush()


def compare(target, case, variants, args, output, samples):
    proof_counts = None
    timed = {name: [] for name in variants}
    work = {}
    limits = ["--work-limit", str(args.work_limit), "--time-limit", args.time_limit]
    for phase, rounds in (("warmup", args.warmups), ("timed", args.pairs), ("work", 1)):
        for index in range(rounds):
            order = ("baseline", "candidate") if index % 2 == 0 else ("candidate", "baseline")
            for name in order:
                log = output / f"{case:02}-{phase}-{index + 1:02}-{name}.log"
                binary, environment = variants[name]
                sample = run(target, name, phase, index + 1, binary, environment, limits, log, samples)
                if proof_counts is None:
                    proof_counts = sample["proof_counts"]
                elif proof_counts != sample["proof_counts"]:
                    raise ValueError(f"selected proof counts differ: {proof_counts} versus {sample['proof_counts']} in {log}")
                if phase == "timed":
                    timed[name].append(sample)
                elif phase == "work":
                    work[name] = sample["completed_tactic_work"]
    print(f"  {sum(proof_counts)} selected proofs", flush=True)
    for name, rows in timed.items():
        walls = [row["wall_seconds"] for row in rows]
        cpus = [row["user_seconds"] + row["system_seconds"] for row in rows]
        print(
            f"  {name:9}  wall {statistics.median(walls):.3f}s [{min(walls):.3f}, {max(walls):.3f}]"
            f"  CPU {statistics.median(cpus):.3f}s [{min(cpus):.3f}, {max(cpus):.3f}]"
            f"  completed tactic work {work[name]:,}",
            flush=True,
        )

    deltas = [
        candidate["wall_seconds"] - baseline["wall_seconds"]
        for baseline, candidate in zip(timed["baseline"], timed["candidate"])
    ]
    print(f"  paired wall deltas (candidate minus baseline), median {statistics.median(deltas):+.3f}s", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", required=True, help="path to an optimized Click executable")
    parser.add_argument("--candidate", help="second executable (default: use the baseline binary)")
    parser.add_argument("--baseline-env", action="append", default=[], metavar="NAME=VALUE")
    parser.add_argument("--candidate-env", action="append", default=[], metavar="NAME=VALUE")
    parser.add_argument("--pairs", type=int, default=5, help="timed pairs per workload (default: 5)")
    parser.add_argument("--warmups", type=int, default=1, help="untimed pairs per workload (default: 1)")
    parser.add_argument("--work-limit", type=int, default=50_000_000)
    parser.add_argument("--time-limit", default="10m", help="Click's containment bound (default: 10m)")
    parser.add_argument("--output", type=Path, help="new report directory (default: a temporary directory)")
    parser.add_argument("targets", nargs="*", type=Path, help="common sidecar, mdtest or project paths")
    args = parser.parse_args()
    if args.pairs < 1 or args.warmups < 0 or args.work_limit < 1:
        parser.error("pairs and work limit must be positive, and warmups must be nonnegative")
    try:
        binaries = {
            "baseline": executable(args.baseline),
            "candidate": executable(args.candidate or args.baseline),
        }
        overrides = {
            "baseline": parse_overrides(args.baseline_env),
            "candidate": parse_overrides(args.candidate_env),
        }
        targets = [path.resolve(strict=True) for path in (args.targets or map(Path, DEFAULT_TARGETS))]
        output = (args.output or Path(tempfile.mkdtemp(prefix="click-benchmark-"))).resolve()
        if args.output is not None:
            output.mkdir(parents=True)
        # Disable dispatch and inherited profiling for both arms. Every run
        # verifies the complete target with the same limits and locked inputs.
        environment = {name: value for name, value in os.environ.items() if name not in CONTROLS}
        environment["CLICK_NO_VERSION_DISPATCH"] = "1"
        variants = {name: (binary, {**environment, **overrides[name]}) for name, binary in binaries.items()}
        hashes = {path: sha256(path) for path in set(binaries.values())}
        metadata = {
            "cwd": str(Path.cwd()),
            "platform": platform.platform(),
            "workload_checkout": workload_checkout(),
            "pairs": args.pairs,
            "warmups": args.warmups,
            "work_limit": args.work_limit,
            "time_limit": args.time_limit,
            "targets": list(map(str, targets)),
            "variants": {
                name: {"binary": str(path), "sha256": hashes[path], "environment_overrides": overrides[name]}
                for name, path in binaries.items()
            },
        }
        (output / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")
        print(f"Report at {output}", flush=True)
        with (output / "samples.jsonl").open("w", encoding="utf-8") as samples:
            for case, target in enumerate(targets, 1):
                print(target, flush=True)
                compare(target, case, variants, args, output, samples)
    except (OSError, ValueError) as error:
        parser.exit(1, f"benchmark-verify: {error}\n")


if __name__ == "__main__":
    main()
