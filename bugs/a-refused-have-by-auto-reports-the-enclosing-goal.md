# A refused `have ... by auto()` reports the enclosing goal

Soundness: not soundness. Nothing false is accepted; this is a diagnostic
defect. The error names the wrong goal and location, so a reader following
[tracing](../docs/concepts/tracing.md) works on a goal that is not the one
refused.

When `auto()` cannot prove a `have` inside a theorem's `ensures ... by` proof,
the error says the checked pure script "could not complete tactic 1
(`have`)", then prints the enclosing `ensures` goal as `goal:` and points at
the theorem header. It omits the `have`'s own goal, its source location, and
the `refused by:` line. The same `have` refused by a simple tactic is
reported correctly: replacing `auto()` with `normalize()` prints
`goal: (word & 1u64) == 0u64` at the `normalize();` line, followed by
`refused by: \`normalize\``.

```c filename=z.c
void unused() {}
```

```click
verifying "z.c";

theorem have_goal(word: uint64, base: uint64) {
    requires to_integer(word) == to_integer(base);
    ensures to_integer(word) == to_integer(base) by {
        have (word & 1) == 0 by auto();
        assumption();
    }
}
```

`click verify` prints:

```text
proof error:
  checked pure script for `have_goal.ensures_0` could not complete tactic 1 (`have`)

goal: word == base
  --> z.click:3:1
  3 | theorem have_goal(word: uint64, base: uint64) {
    | ^^^^^^^
```

The `have` is false (nothing bounds `word & 1`), so the refusal is right;
only the report is wrong.

## Acceptance criteria

- The error for the reproduction prints `goal: (word & 1u64) == 0u64` (the
  `have`'s goal, in the spelling the `normalize()` variant already uses) and
  points at the `have` or its `auto();`, not the theorem header.
- It ends with `refused by:` naming `auto` as smart, as for other smart
  refusals.
- A regression keeps this source pattern: a `have ... by auto()` that fails
  inside a theorem's `ensures ... by` block.
