#!/usr/bin/env python3
"""Summarize a nightly run: what failed, what is new, and how to reproduce it.

Reads the result directories the nightly jobs fill when
`CLICK_NIGHTLY_REPORT_DIR` is set (`docs/internals/testing.md`,
"Nightly report"):

  *.jsonl      one record per mdtest fixture, example project, or failed
               audit site (`src/nightly_report.rs`)
  junit-*.xml  nextest's JUnit results for each nightly test run
  phases.tsv   `name<TAB>seconds<TAB>exit status` per phase
  jobs.tsv     `job<TAB>result` written by the workflow
  counts.tsv   `audit<TAB>outcome<TAB>count` from `scripts/lowering-audits.sh`,
               with `fact-stability.tsv` holding that audit's own records

and writes `report.md` and `report.json` to `--out`. With `--previous` (the
last night's `report.json`) each failure is marked new or persisting, and
failures that ran clean tonight are listed as fixed.

A fact-stability `differs` or `paths` line is a failure: it breaks a rule
lowering enforces. The raise/lower round trip is tracked, not enforced: its
counts are listed beside the previous night's, and a rise in an outcome that
is not `same` is flagged.
"""
import argparse
import json
import os
import re
import sys
import xml.etree.ElementTree as ElementTree
from pathlib import Path

SUMMARY_LIMIT = 300
SLOWEST = 15
UNIT_ENV = "RUST_MIN_STACK=8388608 CLICK_NIGHTLY=1"
# The aggregate tests whose fixtures are recorded one by one in *.jsonl.
# The checks each workflow job records, to tell a job that failed without
# recording any of them (a build error, a crash, a timeout).
JOB_KINDS = {
    "nightly": {"mdtest", "example", "test", "clippy"},
    "audit": {"audit"},
    "lowering": {"lowering"},
}
# The lowering audits' phases, and the fact-stability outcomes that fail.
LOWERING_AUDITS = {"fact-stability": "scripts/fact-stability.sh", "raise-lower": "scripts/raise-lower.sh"}
ENFORCED = {("fact-stability", "differs"), ("fact-stability", "paths")}
# The outcomes whose rise is flagged: everything but a faithful round trip.
TRACKED_GOOD = {"same"}
HARNESSES = {("mdtests", "mdtests"): "mdtest", ("examples", "example_projects"): "example"}


def shell_quote(word):
    if re.fullmatch(r"[A-Za-z0-9_./:=@%+-]+", word):
        return word
    return "'" + word.replace("'", "'\\''") + "'"


def nextest_target(binary):
    """The cargo target flags that select a nextest binary id."""
    if "::" not in binary:
        return "--lib"
    _, name = binary.split("::", 1)
    if name.startswith("bin/"):
        return "--bin " + name[len("bin/"):]
    return "--test " + name


def reproduce(kind, name, binary=None):
    if kind == "lowering":
        return LOWERING_AUDITS[name.split(" ", 1)[0]]
    if kind == "mdtest":
        return f"RUST_MIN_STACK=8388608 MDTEST_FILTER={shell_quote(name)} cargo test --test mdtests -- --exact mdtests"
    if kind == "example":
        return f"RUST_MIN_STACK=8388608 CLICK_EXAMPLE={shell_quote(name)} cargo test --test examples -- --exact example_projects"
    if kind == "audit":
        location = re.fullmatch(r"(.+):(\d+):(\d+)", name)
        path = location.group(1) if location else name
        claim = f" --claim {shell_quote(name)}" if location else ""
        return f"cargo run --release --bin click -- audit{claim} {shell_quote(path)}"
    if kind == "test":
        return (f"{UNIT_ENV} cargo nextest run --run-ignored all {nextest_target(binary)} "
                f"-E {shell_quote(f'test(={name})')}")
    if kind == "clippy":
        return "cargo clippy --all-targets -- -D warnings"
    return "scripts/check.sh --nightly"


def first_lines(text, limit=SUMMARY_LIMIT):
    """The diagnostic's first meaningful line, shortened for one table row."""
    if not text:
        return ""
    lines = [line.strip() for line in text.splitlines()]
    # A Rust panic: the message follows `panicked at <location>:`.
    location = None
    for index, line in enumerate(lines):
        if "panicked at" in line:
            location = line.split("panicked at", 1)[1].strip().rstrip(":")
            rest = [l for l in lines[index + 1:] if l and "panicked at" not in l]
            if rest:
                lines = rest
            break
    lines = [l for l in lines if l and not l.startswith(("stack backtrace", "note: run with"))]
    if not lines:
        return ""
    line = lines[0]
    # A test that prints the Click source it checked, `assert!(.., "{expanded}")`,
    # has no reason in its message: name where it failed instead.
    if location and re.match(r'(verifying|import) "', line):
        return f"panicked at {location}; the message is the Click source it checked"
    # A `ClickError` printed with `{:?}` carries its diagnostic as `message`.
    line = re.sub(
        r'ClickError \{ message: "(.*?)", (?:rendered|kind|failed_tactic):.*',
        lambda m: m.group(1).replace('\\"', '"').replace("\\n", " "),
        line,
    )
    # A header line that ends in a colon introduces the reason on the next.
    if line.endswith(":") and len(lines) > 1:
        line = f"{line} {lines[1]}"
    # An mdtest diagnostic restates its fixture path first.
    line = re.sub(r"^`[^`]*\.md` ", "", line)
    return line if len(line) <= limit else line[: limit - 1] + "…"


def signature(summary):
    """A key that groups failures with the same diagnostic shape."""
    text = re.sub(r"`[^`]*`", "`…`", summary)
    text = re.sub(r"\d+", "N", text)
    # Keep the reason, not the claim and tactic path that precede it.
    text = re.split(r": (?=[^:]*$)", text, maxsplit=1)[-1] if text.count(": ") > 2 else text
    return text[:120]


def read_jsonl(directory):
    for path in sorted(directory.glob("*.jsonl")):
        for line in path.read_text().splitlines():
            if line.strip():
                yield json.loads(line)


def read_junit(directory):
    """Yield (binary, test name, seconds, failure text or None)."""
    for path in sorted(directory.glob("junit-*.xml")):
        try:
            root = ElementTree.parse(path).getroot()
        except ElementTree.ParseError as error:
            print(f"warning: unreadable {path}: {error}", file=sys.stderr)
            continue
        for case in root.iter("testcase"):
            binary = case.get("classname") or ""
            name = case.get("name") or ""
            seconds = float(case.get("time") or 0)
            failure = None
            for tag in ("failure", "error"):
                element = case.find(tag)
                if element is not None:
                    parts = [element.get("message") or "", element.text or ""]
                    for output in ("system-err", "system-out"):
                        found = case.find(output)
                        if found is not None and found.text:
                            parts.append(found.text)
                    failure = "\n".join(p for p in parts if p) or tag
                    break
            yield binary, name, seconds, failure


def read_tsv(path):
    if not path.is_file():
        return []
    return [line.split("\t") for line in path.read_text().splitlines() if line.strip()]


def read_counts(directory):
    counts = {}
    for row in read_tsv(directory / "counts.tsv"):
        counts[(row[0], row[1])] = int(row[2])
    return counts


def first_record(directory, audit, outcome):
    """The fixture of the first `outcome` record `audit` wrote."""
    for row in read_tsv(directory / f"{audit}.tsv"):
        if row[0].startswith(outcome):
            return row[4] if len(row) > 4 else row[-1]
    return None


def collect(directories):
    failures, ran, timings, phases, jobs = {}, set(), [], [], []
    counts = {}
    harness_failed = {"mdtest": False, "example": False}
    for directory in directories:
        for record in read_jsonl(directory):
            key = f"{record['kind']}:{record['name']}"
            ran.add(key)
            if record.get("seconds"):
                timings.append((record["seconds"], key))
            if not record.get("passed"):
                harness_failed[record["kind"]] = True
                failures[key] = {
                    "kind": record["kind"],
                    "name": record["name"],
                    "summary": first_lines(record.get("message")),
                    "seconds": record.get("seconds"),
                    "reproduce": reproduce(record["kind"], record["name"]),
                }
        for phase in read_tsv(directory / "phases.tsv"):
            phases.append({"name": phase[0], "seconds": int(phase[1]), "status": int(phase[2])})
        jobs.extend(read_tsv(directory / "jobs.tsv"))
        for (audit, outcome), count in read_counts(directory).items():
            counts[(audit, outcome)] = count
            key = f"lowering:{audit} {outcome}"
            if (audit, outcome) not in ENFORCED:
                continue
            ran.add(key)
            if count:
                example = first_record(directory, audit, outcome)
                failures[key] = {
                    "kind": "lowering", "name": f"{audit} {outcome}",
                    "summary": f"{count} `{outcome}` lowerings" + (f"; first in {example}" if example else ""),
                    "seconds": None, "reproduce": reproduce("lowering", audit),
                }
    for directory in directories:
        for binary, name, seconds, failure in read_junit(directory):
            short_binary = binary.split("::", 1)[-1] if "::" in binary else binary
            harness = HARNESSES.get((short_binary, name))
            if harness and (failure is None or harness_failed[harness]):
                # Its fixtures are reported one by one; the aggregate adds
                # nothing unless it failed without a failing fixture.
                continue
            key = f"test:{binary} {name}"
            ran.add(key)
            timings.append((seconds, key))
            if failure is not None:
                failures[key] = {
                    "kind": "test",
                    "name": f"{binary} {name}",
                    "summary": first_lines(failure),
                    "seconds": round(seconds, 2),
                    "reproduce": reproduce("test", name, binary),
                }
    for phase in phases:
        if phase["name"] in LOWERING_AUDITS:
            key = f"lowering:{phase['name']} run"
            ran.add(key)
            if phase["status"] != 0:
                failures[key] = {
                    "kind": "lowering", "name": f"{phase['name']} run",
                    "summary": f"the mdtest corpus exited {phase['status']} under the audit; "
                               "an audit must not change a proof's outcome",
                    "seconds": phase["seconds"], "reproduce": reproduce("lowering", phase["name"]),
                }
        if phase["name"] == "clippy" and phase["status"] != 0:
            failures["clippy:clippy"] = {
                "kind": "clippy", "name": "clippy",
                "summary": f"cargo clippy exited with {phase['status']}",
                "seconds": phase["seconds"], "reproduce": reproduce("clippy", "clippy"),
            }
    return failures, ran, timings, phases, jobs, counts


def lowering_counts(counts, previous):
    """Tonight's audit counts beside the previous night's."""
    before = {(c["audit"], c["outcome"]): c["count"] for c in (previous or {}).get("counts", [])}
    rows = []
    for (audit, outcome), count in counts.items():
        earlier = before.get((audit, outcome))
        rows.append({
            "audit": audit, "outcome": outcome, "count": count, "previous": earlier,
            "rose": earlier is not None and count > earlier and outcome not in TRACKED_GOOD,
        })
    return rows


def build(arguments):
    directories = [Path(d) for d in arguments.input if Path(d).is_dir()]
    failures, ran, timings, phases, jobs, counts = collect(directories)
    for job, result in jobs:
        own = JOB_KINDS.get(job, set())
        if result not in ("success", "skipped") and not any(
            f["kind"] in own for f in failures.values()
        ):
            key = f"job:{job}"
            failures[key] = {
                "kind": "job", "name": job,
                "summary": f"the `{job}` job ended `{result}` without recording a failing check; see the run log",
                "seconds": None, "reproduce": reproduce("job", job),
            }
    previous = None
    if arguments.previous and Path(arguments.previous).is_file():
        previous = json.loads(Path(arguments.previous).read_text())
    previous_ids = {f["id"] for f in previous["failures"]} if previous else set()
    audit_ran = any(job == "audit" and result in ("success", "failure") for job, result in jobs)
    lowering_ran = any(job == "lowering" and result in ("success", "failure") for job, result in jobs)
    for key, failure in failures.items():
        failure["id"] = key
        failure["status"] = "persisting" if key in previous_ids else ("new" if previous else "unknown")
        failure["signature"] = signature(failure["summary"])
    fixed = sorted(
        key for key in previous_ids - failures.keys()
        if key in ran or (key.startswith("audit:") and audit_ran)
        or (key.startswith("lowering:") and lowering_ran)
    )
    not_run = sorted(previous_ids - failures.keys() - set(fixed))
    groups = {}
    for failure in failures.values():
        groups.setdefault(failure["signature"], []).append(failure["id"])
    report = {
        "commit": arguments.commit,
        "run_url": arguments.run_url,
        "date": arguments.date,
        "previous_commit": previous.get("commit") if previous else None,
        "jobs": [{"job": job, "result": result} for job, result in jobs],
        "phases": phases,
        "failures": sorted(failures.values(), key=lambda f: (f["status"] != "new", f["kind"], f["name"])),
        "fixed": fixed,
        "not_run": not_run,
        "groups": sorted(
            ({"signature": key, "ids": sorted(ids)} for key, ids in groups.items() if len(ids) > 1),
            key=lambda group: -len(group["ids"]),
        ),
        "slowest": [{"id": key, "seconds": round(seconds, 2)}
                    for seconds, key in sorted(timings, reverse=True)[:SLOWEST]],
        "counts": lowering_counts(counts, previous),
    }
    return report


def duration(seconds):
    seconds = int(seconds)
    return f"{seconds // 3600}h{seconds % 3600 // 60:02d}m" if seconds >= 3600 else f"{seconds // 60}m{seconds % 60:02d}s"


def cell(text):
    return text.replace("|", "\\|").replace("\n", " ")


def prose(text):
    """Table text outside code: `<state A>` must not read as an HTML tag."""
    return cell(text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;"))


def render(report):
    failures = report["failures"]
    new = [f for f in failures if f["status"] == "new"]
    lines = [f"# Nightly {report['date']} at {report['commit'][:12]}", ""]
    if report["run_url"]:
        lines.append(f"Run: {report['run_url']}")
    counts = f"**{len(failures)} failing**"
    if report["previous_commit"]:
        counts += (f": {len(new)} new, {len(failures) - len(new)} persisting; "
                   f"{len(report['fixed'])} fixed since {report['previous_commit'][:12]}")
    lines += [counts, ""]
    rose = [c for c in report["counts"] if c["rose"]]
    if rose:
        lines += ["**Lowering audits rose:** " + ", ".join(
            f"{c['audit']} `{c['outcome']}` {c['previous']} → {c['count']}" for c in rose), ""]
    if report["jobs"] or report["phases"]:
        lines += ["| Job or phase | Result | Time |", "|---|---|---|"]
        for job in report["jobs"]:
            lines.append(f"| job `{job['job']}` | {job['result']} | |")
        for phase in report["phases"]:
            result = "passed" if phase["status"] == 0 else f"exit {phase['status']}"
            lines.append(f"| `{phase['name']}` | {result} | {duration(phase['seconds'])} |")
        lines.append("")

    def table(rows):
        out = ["| Check | First line | Reproduce |", "|---|---|---|"]
        for f in rows:
            out.append(f"| {f['kind']} `{cell(f['name'])}` | {prose(f['summary'])} | `{cell(f['reproduce'])}` |")
        return out + [""]

    if report["previous_commit"]:
        lines += ["## New failures", ""]
        lines += table(new) if new else ["None.", ""]
    if report["groups"]:
        lines += ["## Failures sharing a diagnostic", ""]
        for group in report["groups"]:
            names = ", ".join(f"`{i.split(':', 1)[1]}`" for i in group["ids"])
            lines.append(f"- {len(group['ids'])} × {prose(group['signature'])}: {names}")
        lines.append("")
    persisting = [f for f in failures if f["status"] != "new"]
    if persisting:
        lines += ["## Persisting failures" if report["previous_commit"] else "## Failures", ""]
        lines += table(persisting)
    if report["fixed"]:
        lines += ["## Fixed since the previous night", ""]
        lines += [f"- `{i}`" for i in report["fixed"]] + [""]
    if report["not_run"]:
        lines += ["## Failing last night, not run tonight", ""]
        lines += [f"- `{i}`" for i in report["not_run"]] + [""]
    if report["counts"]:
        lines += ["## Lowering audits", "",
                  "Fact-stability `differs` and `paths` fail the night; the raise/lower "
                  "counts are tracked, and a rise in any outcome but `same` is flagged.", "",
                  "| Audit | Outcome | Tonight | Previous | Change |", "|---|---|---|---|---|"]
        for c in report["counts"]:
            earlier = "" if c["previous"] is None else str(c["previous"])
            change = "" if c["previous"] is None else f"{c['count'] - c['previous']:+d}"
            if c["rose"]:
                change = f"**{change}** (rose)"
            lines.append(f"| {c['audit']} | `{c['outcome']}` | {c['count']} | {earlier} | {change} |")
        lines.append("")
    if report["slowest"]:
        lines += ["## Slowest checks", "", "| Check | Time |", "|---|---|"]
        lines += [f"| `{cell(s['id'])}` | {s['seconds']:.1f}s |" for s in report["slowest"]]
        lines.append("")
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--input", action="append", default=[], help="a result directory; may repeat")
    parser.add_argument("--previous", help="the previous night's report.json")
    parser.add_argument("--out", required=True)
    parser.add_argument("--commit", default=os.environ.get("GITHUB_SHA", "unknown"))
    parser.add_argument("--date", default="")
    parser.add_argument("--run-url", default="")
    arguments = parser.parse_args()
    report = build(arguments)
    out = Path(arguments.out)
    out.mkdir(parents=True, exist_ok=True)
    (out / "report.json").write_text(json.dumps(report, indent=1) + "\n")
    markdown = render(report)
    (out / "report.md").write_text(markdown + "\n")
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a") as handle:
            handle.write(markdown + "\n")
    print(f"nightly report: {len(report['failures'])} failing, {len(report['fixed'])} fixed")


if __name__ == "__main__":
    main()
