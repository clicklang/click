# A refused Rust panic check under Integer arithmetic reports `goal: 0 == 1`

Soundness: diagnostic only. The proof is refused, as it may be; the defect is
that the refusal names a goal it did not try, so neither the message nor the
trace shows the comparison that failed.

When `execute()` cannot prove a Rust overflow check, the refusal should name
that check's obligation as the implicit `auto` tried it. With
`arithmetic "integer";` added to `examples/rust-usize/arithmetic.click`, the
`add` proof is refused with:

```text
`execute()` is missing prerequisite (Rust add panic check)
could not show `__rust_checked_0 <= (18446744073709551615u64 - __rust_checked_1)` from no fact about `__rust_checked_0`, `__rust_checked_1`
...
goal: 0 == 1
available premises at the failed check (showing 1 of 1):
  integer-condition(machine-integer<UInt64>(x) <= (18446744073709551615-machine-integer<UInt64>(y))) is true
```

The `goal:` line reads `0 == 1`, not the native check
`x <= 18446744073709551615u64 - y` over the operands, and the "no fact about"
line names the `__rust_checked_*` temporaries although the trace shows them
assigned from `x` and `y`. `--trace-proof add` adds no step inside the
implicit `auto`, so the reader cannot tell whether the obligation was spelled
over the temporaries, over `x` and `y`, or not at all.

The proof itself may also be a miss: the only premise is the Integer reading
of `requires x <= 18446744073709551615u64 - y;`, and the documented `auto`
proves a `uint64` order goal through its Integer reading, observing
`18446744073709551615u64 - y` by `uint64_subtract_to_integer`. Whether that
should close this check is a separate question; this report is about the
diagnostic.

## Reproduction

From the repository root:

```sh
printf '\narithmetic "integer";\n' >> examples/rust-usize/arithmetic.click
click verify examples/rust-usize
click verify --trace-proof add examples/rust-usize/arithmetic.click
```

## Acceptance criteria

- The refusal's `goal:` names the obligation the implicit `auto` tried,
  spelled over the function's own operands where the temporaries hold them.
- A regression reproduces the refused check (the `add` shape, under the
  directive) and asserts the message does not contain `goal: 0 == 1`.
