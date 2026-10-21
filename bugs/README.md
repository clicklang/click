# Verifier bugs

A bug is a reproduced defect in behavior Click already claims to support.
Agents file a bug here only after the user agrees to it, as with roadmap
entries in `issues/`.

Prefer to fix a small defect in the task thread that found it: put its
reproduction and acceptance criteria in the fix PR, and land its regression
with the fix. A bug file hands a defect off: one that is unrelated to the
current work or too large to fix now. Describe it to the user with its
reproduction and ask before filing. Other contributors pick up the files here,
so one you are about to fix only distracts them.

Examples include accepting a false claim, rejecting a documented valid proof
operation, crashes or hangs, violated work budgets, disagreement between proof
tools, and inaccurate, misleading, or unbounded diagnostics. Use the
[proof-failure triage guide](../docs/concepts/proof-failure-triage.md) to classify
the failure. Missing features and new design directions belong to the roadmap,
not here; report ambiguous cases to the user rather than bypassing issue policy.

Reproduce the defect before filing. A one-off observation or a suspicion from
reading code should be reported to the user as such. File one kebab-case `.md`
per independent bug, stating:

- the violated invariant;
- a small reproduction and intended regression that preserve the relevant
  original source pattern; and
- concrete acceptance criteria.

Directly under the title, state `Soundness: <label>.` with a one-paragraph
argument, using the labels defined in
[`issues/README.md`](../issues/README.md). A bug that lets a false claim
verify is `unsound`. Put `Priority: P1.` above its Soundness paragraph: it
blocks launch.

Write enough for a fresh contributor to act without the originating chat.
Tell the user what was filed. Delete the file when its fix, regression coverage,
and relevant documentation land.

The files in this directory are the backlog. This README does not maintain a
separate bug list.

## Odd and even assignments

Split bugs reproducibly by hashing each bug's filename, including its `.md`
extension and excluding the `bugs/` directory, with SHA-256 over UTF-8 bytes.
Interpret the digest's final hexadecimal digit as a number: an odd value
(`1`, `3`, `5`, `7`, `9`, `b`, `d`, or `f`) assigns the bug to **odd**;
an even value (`0`, `2`, `4`, `6`, `8`, `a`, `c`, or `e`) assigns it to **even**.
This gives a roughly random split that remains stable when other bugs are added
or removed. Keep the filename unchanged while work is assigned; do not rename a
bug to change its group. The group is independent of priority.

`README.md` is not a bug. Companion reproductions such as `.click` files follow
their bug report's assignment rather than receiving a separate assignment.
When assigned one group, select new bugs only from that group.

List the current assignments from the repository root:

```sh
python3 - <<'PY'
import hashlib
from pathlib import Path

for path in sorted(Path("bugs").glob("*.md")):
    if path.name == "README.md":
        continue
    digest = hashlib.sha256(path.name.encode("utf-8")).hexdigest()
    group = "odd" if int(digest[-1], 16) % 2 else "even"
    print(f"{group}\t{path.name}")
PY
```
