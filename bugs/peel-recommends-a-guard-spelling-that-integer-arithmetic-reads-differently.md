# `peel` recommends a guard spelling that Integer arithmetic reads differently

Soundness: diagnostic only. `peel` refuses; the defect is that its refusal
tells the author to list a guard whose written form, under Integer-default
specification arithmetic, states a different proposition from the one `peel`
needs.

A `peel(prefix(...)) using { ... }` refusal names the guards that would
decide its range, as source text. A comparison that does arithmetic compares
exact Integers, so the named text is not the native guard `peel` reads. In
`examples/rust-iter-references/sum.click`, a proof that lists the guard
exactly as the message asks is refused with the same message:

```text
`peel(prefix(...)) using` found no listed guard that decides the range. The empty-range equation needs `bytes.len() - iter_remaining + 1u64 <= 0u64`; the append-last-cell equation needs `bytes.len() - iter_remaining < 18446744073709551615u64`.

tactic@38:
  peel(prefix(bytes, (bytes.len() - iter_remaining) + 1u64)) using {
      0u64 <= (bytes.len() - iter_remaining);
      (bytes.len() - iter_remaining) < 18446744073709551615u64;
  };
```

The listed `(bytes.len() - iter_remaining) < 18446744073709551615u64` reads
as `to_integer(bytes.len()) - to_integer(iter_remaining) <
18446744073709551615`, while `peel` wants the native comparison of the
machine endpoint, which is spelled over exact observations:
`to_integer(bytes.len() - iter_remaining) < to_integer(18446744073709551615u64)`,
as the example's proof now lists it. Following the message's advice fails. (That `peel` reads only the native
guard is the functional gap; this report is about the advice.)

## Reproduction

In `examples/rust-iter-references/sum.click`, in the loop's `peel` and the two
`have` steps before it, replace the guards
`to_integer(0u64) <= to_integer(bytes.len() - iter_remaining)` and
`to_integer(bytes.len() - iter_remaining) < to_integer(18446744073709551615u64)`
with the spellings the message names, `0u64 <= (bytes.len() - iter_remaining)`
and `(bytes.len() - iter_remaining) < 18446744073709551615u64`, then run:

```sh
click verify examples/rust-iter-references
```

## Acceptance criteria

- A `peel` refusal does not recommend a guard whose written form reads as a
  different proposition: it names the guard in a spelling that lowers to what
  `peel` reads, such as one over exact observations.
- A regression runs the refused `peel` and checks the
  message.
