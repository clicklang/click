# A C-valued range fold over `uint64` bounds lowers to no path

## Violated invariant

Type validation accepts a range fold whose bounds are both `uint64`
("range fold bounds must both be int32 or both be uint64"), and a fold with
an `Integer` accumulator over such bounds evaluates. A fold with a C-valued
accumulator over the same bounds, or over `int32` bounds with a `uint64`
accumulator, is accepted and then lowers to zero paths, reported only as
"the kernel lowering produced 0 paths, not one".

## Reproduction

```c
int32 g(uint8 p[], uint8 x) {
    int32 count;
    count = 0;
    if (p[0] == x) { count = count + 1; }
    if (p[1] == x) { count = count + 1; }
    return count;
}
```

```click
function my_count(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + if bytes[k] == value { 1 } else { 0 }
    })
}

int32 g(uint8 p[], uint8 x) {
    views p[0..2];
    ensures result == my_count(p, 0u64, 2u64, x) by {
        execute();
        unfold(my_count(p, 0u64, 2u64, x));
        simp();
    }
}
```

`unfold` fails: "could not lower defining equation for `my_count`: the
kernel lowering produced 0 paths, not one". The same failure occurs with
`int32` bounds and a `uint64` accumulator (`-> uint64`, `0u64`, `1u64`). With
`int32` bounds and an `int32` accumulator the proof verifies.

`evaluate_spec_range_fold_paths_in` (`src/kernel/spec.rs`) skips any bound
that is not `CValue::Int32`, and its symbolic case builds the `int32`-only
`Bitvector32Term::range_fold`. This is why the standard library's
`byte_count` keeps `int32` bounds while the other byte helpers take `size_t`.

## Intended regression

The program above verifies, and so does its `uint64`-accumulator variant.
Until a `uint64` fold term exists, an unsupported combination is refused by
validation or lowering with a diagnostic naming the fold, not a zero-path
count.

## Acceptance criteria

- A C-valued fold over `uint64` bounds evaluates for constant bounds and has
  a symbolic term for symbolic bounds, or is refused with a named reason.
- `byte_count` can then take `size_t` bounds like the other byte helpers.
