# `close_invariants` under a disjunctive guard certifies each entry path differently

Soundness: no soundness impact. A valid proof is refused and nothing false
is accepted. The defect is a disagreement between one source tactic's
certificates on two paths, with no trace to show either.

One source tactic on one proof path should produce one certificate, and a
refusal should come with a trace (`docs/concepts/tracing.md`). A loop whose
guard is `a > 0 || b > 0` enters its body along two C paths, one per
disjunct. With the Integer measure `decreases a + b;` and a `preserve` proof
that states `have 0 < a + b` by cases, the body's `close_invariants()` is
refused:

```text
proof error:
  `enters_either_way.contract` produced different certificates for the same proof path

tactic@29:
  close_invariants();
```

`click verify --trace-proof enters_either_way` (with or without
`--trace-to`) prints only `proof trace unavailable: no checked path was
retained for this failure`. Stating the bound over the exact observation of
the machine sum, `have 0 < to_integer(a + b) by { ... }`, makes the same
proof verify; `mdtests/loop_disjunctive_guard_entry_join.md` is written that
way. Before Integer-default arithmetic the native `have 0 < a + b` verified.

## Reproduction

From the repository root:

```sh
cd bugs
click verify close-invariants-under-a-disjunctive-guard-certifies-each-entry-path-differently.click
click verify --trace-proof enters_either_way close-invariants-under-a-disjunctive-guard-certifies-each-entry-path-differently.click
```

The companion `.c` file is
`close-invariants-under-a-disjunctive-guard-certifies-each-entry-path-differently.c`.

## Acceptance criteria

- `close_invariants()` yields one certificate for both entry paths, or the
  refusal names the obligation whose certificate differs and a trace shows
  both.
- A regression verifies the companion sidecar as written.
