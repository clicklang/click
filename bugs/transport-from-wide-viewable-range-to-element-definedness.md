# `transport` cannot carry a wide `viewable` range to one element's definedness

## Violated invariant

A `viewable` range over a `size_t` (`uint64`) bound supports the same
reasoning as one over an `int32` bound. Transporting
`at(function.entry, viewable(bytes[0..n + 1]))` to `defined(bytes[k])` for an
in-range `k` succeeds when `n` and `k` are `int32`, and is refused when they
are `uint64`, with a diagnostic that blames a missing effect fact although
the frontier differs from entry only by a local declaration.

## Reproduction

```c
uint64 f(uint8 bytes[], uint64 n) {
    uint64 x;
    x = 0;
    return x;
}
```

```click
uint64 f(uint8 bytes[], uint64 n) {
    requires n < 18446744073709551615u64;
    requires viewable(bytes[0..n + 1u64]);
    ensures result == 0u64 by {
        execute_until(statement(1));
        have forall (k: uint64) { k < n + 1u64 implies defined(bytes[k]) } by {
            intro();
            intro();
            transport(
                at(function.entry, viewable(bytes[0..n + 1u64])),
                defined(bytes[k])
            ) using {
                k < n + 1u64;
                at(function.entry, viewable(bytes[0..n + 1u64]));
            }
        }
        execute();
        simp();
    }
}
```

The `transport` fails with "found no frame evidence carrying its source fact
to the target's state ... no effect fact at this frontier relates the two
states". The same proof with `int32 n`, `0 <= n and n < 2147483647`,
`int32 k`, and `0 <= k` premises verifies.

`cstr_readable` and `strlen` now state their lengths as `size_t`, so this is
the transport a C-string proof needs for `forall (k: uint64) { k < len + 1u64
implies defined(bytes[k]) }`. The C-string mdtests route around it by
instantiating the entry universal and transporting the single
`defined(bytes[k])` fact.

## Intended regression

An mdtest with the program above, verifying, beside the existing `int32`
form.

## Acceptance criteria

- The transport's frame step places a `uint64`-indexed element in a wide
  `viewable` range by the same membership rule `pointer_access_in_wide_range`
  applies to accesses.
- A `k` that is not below the range end is still refused.
- The refusal for a genuinely missing frame no longer names an effect fact
  when the two states differ only by allocation of an unrelated local.
