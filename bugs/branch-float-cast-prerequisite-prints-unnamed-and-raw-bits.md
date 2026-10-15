# A float-cast branch prerequisite prints `<unnamed A>` and raw bits

Soundness: incomplete. The refusal is correct; only its diagnostic is unusable.
No false acceptance is involved.

A C condition that casts a non-constant `double` to `int32` owes the cast's
range obligations (`isfinite(x)`, `x >= -2^31`, `x < 2^31`;
`add_float_to_integer_obligations` in `src/kernel/eval/expression.rs`). When
`branch` cannot decide one, it refuses with `missing condition prerequisite`.
The refusal names the parameter `<unnamed A>` instead of `d`, and it prints the
bound as the raw IEEE bits `13970166044103278592u64` instead of
`-2147483648.0`. A user cannot tell which fact to state.

## Reproduction

```c filename=branch_float_cast.c
int32 positive(double d) {
    if ((int32) d > 0) {
        return 1;
    }
    return 0;
}
```

```click
verifying "branch_float_cast.c";

int32 positive(double d) {
    requires isfinite(d);
    ensures result >= 0;
} by {
    branch then { step(); simp(); } else {}
    step();
    simp();
}
```

The output is:

```
`branch` is missing condition prerequisite
`<unnamed A> >= 13970166044103278592u64`
```

Without the `requires`, the first missing prerequisite reads
`isfinite(<unnamed A>)`. A `have` of the bound that fails prints the goal as
`at(statement(0).entry, d) >= 13970166044103278592u64`.

## Acceptance criteria

- The refusal names the obligation over the caller's source names
  (`isfinite(d)`, `d >= -2147483648.0`), in a form that can be copied into a
  `have` before the `branch`.
- Floating-point constants in diagnostics print as decimal literals, not bit
  patterns.
- This reproduction stays as an mdtest expecting the readable refusal.
