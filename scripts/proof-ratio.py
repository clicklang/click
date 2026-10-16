#!/usr/bin/env python3
"""Report each example's proof-to-code ratio against the proof-size target.

The target is about 20 lines of Click proof per line of C it proves
(`docs/internals/verification-efficiency.md`, "Proof size and speed
targets"). Lines are what the target counts, so they decide which examples
are over it. Tokens are reported beside them because a proof line is often
much longer than a line of C: a proof that crams its steps onto long lines
meets a line target it would miss by tokens. A token is an identifier or
number, or one punctuation character.

Comments and blank lines are not counted on either side. Proof is counted
over an example's tracked `.click` files; code over the sources those files
name in `verifying "...";`, counted once per example even when several
sidecars verify the same file. Headers the sources include are not counted.

The report never fails the gate. `--over` lists only the examples over the
target.
"""

import pathlib
import re
import subprocess
import sys

TARGET = 20
VERIFYING = re.compile(r'^\s*verifying\s+"([^"]+)"', re.MULTILINE)
COMMENT = re.compile(r"/\*.*?\*/|//[^\n]*", re.DOTALL)
TOKEN = re.compile(r"\w+|[^\s\w]")


def measure(text):
    """Lines and tokens of `text` outside comments."""
    code = COMMENT.sub(lambda comment: "\n" * comment.group(0).count("\n"), text)
    lines = sum(1 for line in code.splitlines() if line.strip())
    return lines, len(TOKEN.findall(code))


def tracked_sidecars(directory):
    listed = subprocess.run(
        ["git", "ls-files", "-z", "--", "*.click"],
        cwd=directory,
        capture_output=True,
        check=True,
    ).stdout.decode()
    return sorted(directory / name for name in listed.split("\0") if name)


def read(path):
    return path.read_text(encoding="utf-8", errors="replace")


def example_size(directory):
    proof_lines = proof_tokens = 0
    sources = set()
    for sidecar in tracked_sidecars(directory):
        text = read(sidecar)
        lines, tokens = measure(text)
        proof_lines += lines
        proof_tokens += tokens
        for name in VERIFYING.findall(text):
            source = (sidecar.parent / name).resolve()
            if source.is_file():
                sources.add(source)
    code = [measure(read(source)) for source in sources]
    return proof_lines, proof_tokens, sum(c[0] for c in code), sum(c[1] for c in code)


def main():
    only_over = "--over" in sys.argv[1:]
    examples = pathlib.Path(__file__).resolve().parent.parent / "examples"
    rows = []
    for directory in sorted(path for path in examples.iterdir() if path.is_dir()):
        proof_lines, proof_tokens, code_lines, code_tokens = example_size(directory)
        if code_lines:
            rows.append(
                (
                    proof_lines / code_lines,
                    proof_tokens / code_tokens,
                    directory.name,
                    proof_lines,
                    code_lines,
                )
            )
    rows.sort(reverse=True)
    over = [row for row in rows if row[0] > TARGET]
    print(
        f"proof size: {len(over)} of {len(rows)} examples over the {TARGET}x line target "
        f"(lines ratio, tokens ratio, proof lines / code lines)"
    )
    for by_lines, by_tokens, name, proof_lines, code_lines in over if only_over else rows:
        marker = "over" if by_lines > TARGET else "    "
        print(
            f"  {marker} {by_lines:6.1f}x  {by_tokens:6.1f}x  "
            f"{proof_lines:6d} / {code_lines:4d}  {name}"
        )


if __name__ == "__main__":
    main()
