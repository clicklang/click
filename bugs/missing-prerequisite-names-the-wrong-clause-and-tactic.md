# A missing call prerequisite names the wrong clause and tactic

Soundness: not soundness. This is a misleading diagnostic; the refusal itself
is correct and nothing false is accepted.

When a call step refuses a precondition, the diagnostic names the callee
clause by ordinal and the refused tactic by index. Both can be wrong. Below,
`first` has two preconditions; the `have` closes the first one, and the step
is refused for the second, `y > 0 or x > 0`. The diagnostic calls it the
"first precondition", and it reports the refusal at "tactic 0" although the
refused `step()` is the second tactic of the proof (the `have` is tactic 0).
A reader looking for the clause or the tactic is sent to the wrong one.

Reproduced on master `2735ec7`:

```c filename=pair.c
int32 first(int32 x, int32 y) {
    return x;
}

int32 caller(int32 a, int32 b) {
    return first(a, b);
}
```

```click
verifying "pair.c";

int32 first(int32 x, int32 y) {
    requires x > 0 or y > 0;
    requires y > 0 or x > 0;
    ensures 1 == 1 by auto;
}

int32 caller(int32 a, int32 b) {
    requires a > 0;
    ensures 1 == 1 by { have a > 0 or b > 0 by simp; step(); step(); simp(); }
}
```

```text
proof error:
  `caller.ensures_0` tactic 0
  `step()` is missing prerequisite (first precondition)
  (b > 0) or (a > 0)
  C statement at pair.c:6:5
  `return first(a, b);`
```

The ordinal looks like a count of the obligations still open at the step
rather than the clause's position in `first`'s contract; the tactic index
looks like it counts from the step's own scope. Both are guesses from the
output and still need confirming in the code.

## Acceptance criteria

- The refusal names `first`'s second precondition, by the same ordinal its
  contract order gives it.
- The refusal names the refused `step()` by its position in the written proof.
- An mdtest pins both with the reproduction above, and a second case where
  the first clause is the refused one still names it first.
