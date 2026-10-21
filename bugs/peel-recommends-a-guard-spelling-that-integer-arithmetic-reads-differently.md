# `peel` recommends a guard spelling that Integer arithmetic reads differently

Soundness: diagnostic only. `peel` refuses; the defect is that its refusal
tells the author to list a guard whose written form, in a file using
`arithmetic "integer";`, states a different proposition from the one `peel`
needs.

A `peel(prefix(...)) using { ... }` refusal names the guards that would
decide its range, as source text. Under the directive a comparison that does
arithmetic compares exact Integers, so the named text is not the native
guard `peel` reads. Migrating `examples/rust-iter-references/sum.click`, the
proof lists the guard exactly as the message asks and is refused with the
same message:

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
machine endpoint. In such a file no source text spells that native guard, so
the message's advice cannot be followed. (That `peel` reads only the native
guard is the functional gap; this report is about the advice.)

## Reproduction

From the repository root, add `arithmetic "integer";` at the end of
`examples/rust-iter-references/sum.click`, prove the first `peel`'s premise
with `have bytes.len() - iter_remaining <= 0u64 by auto();` before it, and
state `have 0u64 <= (bytes.len() - iter_remaining) by auto();` before the
loop's `peel`, then run:

```sh
click verify examples/rust-iter-references
```

## Acceptance criteria

- Under `arithmetic "integer";`, a `peel` refusal does not recommend a guard
  whose written form reads as a different proposition: it names the guard in
  a spelling that lowers to what `peel` reads, or says the guard has no
  spelling in this file.
- A regression runs the refused `peel` under the directive and checks the
  message.
