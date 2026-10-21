---
name: verifier-design
description: Place a proposed verifier change in the fast part or the slow part and check it against that part's cost rule. Use before proposing, implementing, or reviewing any change that makes the verifier do more work — new reasoning in the kernel, a new rule in `decide`, a new search in a tactic, or a new index — and whenever a thread suggests "change the verifier so that it does X".
---

# Verifier design check

The rules are in `docs/internals/verifier-design.md`. Read it first. This
skill is the procedure for applying them.

## 1. Name the part

Find the part the change touches in the table in "The parts". Use the
"Vocabulary" table to translate a mechanism name (order walk, difference
graph, memory resolution, premise selection) into its part. If the change
touches more than one part, do this check for each.

## 2. Prefer the slow part

If the change adds reasoning, first try to place it in the slow part: a new
strategy inside `simp`, `arithmetic`, or `auto`, or a search helper that fills
an argument a tactic already accepts. Put it in the fast part only when every
proof needs it on every step, and say why.

## 3. Check the rule

For a fast-part change, name for each read:

- the index it reads, and the key built from the operation's input;
- why no collection that grows with the program, path, facts, snapshots, or
  resources is scanned, including facts related to the input;
- the scaling test: work at several sizes as unrelated input grows, and as
  related input grows (a longer chain, a larger class, more stores between
  two loads), measured in deterministic work units
  (`instrumentation::measure_deterministic_work`), not wall time.

For a slow-part change, name:

- the budget it runs under and its bounded failure message;
- what `click expand` writes in its place;
- the explicit syntax that lets an author write that result with no search.
  If it doesn't exist, adding it is part of the change.

## 4. Report the check

Begin the proposal, or the pull request description, with:

```text
Design check
- Part: <part> (fast | slow)
- Why this part: <one sentence>
- Fast: index and key per read; scaling test name and sizes
- Slow: budget; what expansion writes; explicit syntax
- Failure: <what a miss or refusal says>
```

A change that can't fill in the fast or the slow line doesn't go in. Report
that to the user instead of implementing it.

## 5. Existing scans

If the change touches code listed under "Fast-part scans" in
`issues/smart-tactics.md`, don't add another scan beside it. Either fix that
scan (index it, or move it to the slow part with an explicit form) or leave
it as it is and say so.
