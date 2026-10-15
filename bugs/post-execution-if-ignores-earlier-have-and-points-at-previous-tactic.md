# A post-execution `if` ignores an earlier `have` and blames the tactic before it

Soundness: incomplete. A true claim is refused and the refusal is misplaced.
No false acceptance is involved.

After `execute()`, a proof `if` over a stable program-point condition (operands
`old(..)` or `x@L`) picks one arm per outcome path
(`checked_outcome_if_value` in `src/surface/proof/proof_object/fixed_state_steps.rs`).
It decides the condition from the outcome's facts, by exact lookup or by the
kernel's condition decision. A `have` written after `execute()` and before the
`if` that states exactly that condition does not count. The arm is selected
before deferred post-execution `have`s run, so the `if` is refused with
`focused outcome does not decide the post-execution \`if\` condition`. That
refusal is reported at the tactic before the `if` (`execute();`, or the
`have`), not at the `if` itself.

## Reproduction

```c filename=pick.c
int32 pick(int32 a, int32 b) {
    if (a > b) {
        return a;
    }
    return b;
}
```

```click
verifying "pick.c";

int32 pick(int32 a, int32 b) {
    requires a > b or a == b;
    ensures result >= a;
} by {
    execute();
    have old(a) >= old(b);
    if old(a) >= old(b) {
        have result == a;
    } else {
        have result == b;
    }
}
```

The output is `focused outcome does not decide the post-execution \`if\`
condition` at `have old(a) >= old(b);`. Moving the `have` (as `have a >= b;`)
before `execute()` verifies.

## Acceptance criteria

- A `have` before a post-execution `if`, in source order, is available when
  the `if` picks its arm, and the reproduction verifies.
- An undecided post-execution `if` is refused at the `if`, naming the condition
  and the path it could not decide.
- The reproduction stays as an mdtest.
