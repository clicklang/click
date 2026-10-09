# An empty `loop` clause on a resource-free loop unrolls to the budget

A `loop` clause is a checked loop rule: the kernel verifies its phases once
and then applies the rule at the source loop. A clause with no `invariant`,
no `decreases`, and no resource frame on a function with no resources should
still be a rule. Instead the annotated loop carries no invariant, effect, or
measure checks, so `execute_c_statement_verification_paths` treats it as an
unannotated `while` and unrolls it in the evaluator until the
256-iteration loop unrolling budget is spent. The run takes about 22 seconds
in a debug build before it fails, with no prompt local failure:

```c
int poll(int x) {
    return x;
}
int spin(int x) {
    while (poll(x) == 0) {
    }
    return 1;
}
```

```click
verifying "r.c";
int32 poll(int32 x) {
    ensures result == x;
} by { step(); simp(); }
int32 spin(int32 x) diverges {
    ensures result == 1;
} by {
    loop diverges {
    }
    step();
    simp();
}
```

`click verify` reports "`loop` stopped at the loop unrolling budget". Here are
some neighbouring cases that are prompt:
- The same loop in a function that `views` a pointer verifies at once: the
  frame gives the annotated loop one effect check.
- Adding `invariant x == x;` to the clause verifies at once.

The dispatch in `src/kernel/loops.rs` that chooses between applying a
verified rule and unrolling tests `!invariant_checks.is_empty() ||
!effect_checks.is_empty() || ...`. A rule with nothing to check therefore
fails that test.

## Regression

Add the program above as an mdtest that is expected to pass, under the gate's
time budget.

## Acceptance

- A `loop` clause with nothing to check is still applied as its verified rule
  and never unrolled.
- The regression verifies in well under a second.
- An unannotated `while` with no clause keeps its current behavior.
