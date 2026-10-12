# Owning one element of a wide array leaves its loads unreadable

Soundness: incomplete. The failure is a refusal: a load the contract plainly
grants is rejected as not fitting its cell, so a valid proof does not verify.
Nothing false is accepted.

## Violated invariant

`owns a[0]` grants the first element of `a`, whatever the element type. For an
`int32*` it does. For an 8-byte element type (`int64*`, `uint64*`) the granted
cell does not hold the element: the first C read of `a[0]` is refused with
"a 8-byte load at `a` did not fit the cell's value". The same function verifies
when the contract says `owns *a` or `owns a[0..1]` instead, so the three
spellings of one element disagree. `views a[0]` fails the same way.

## Reproduction

`c.c`:

```c
int32 f(uint64* a, uint64 n) {
    if (a[0] < n) {
        return 1;
    }
    return 0;
}
```

`c.click`:

```click
verifying "c.c";

int32 f(uint64* a, uint64 n) {
    owns a[0];
} by {
    execute();
    simp();
}
```

`click verify c.click` reports:

```text
`f.contract` tactic 0: `branch` could not evaluate the C condition: a 8-byte load at `a` did not fit the cell's value.
```

Replacing `owns a[0];` with `owns *a;` or `owns a[0..1];` verifies. With
`int64` in place of `uint64` the result is the same; with `int32` the original
form verifies.

## Acceptance criteria

- The reproduction verifies with `owns a[0]` and with `views a[0]` for
  `int64*` and `uint64*`, keeping the original `a[0]` spelling in the contract.
- A regression mdtest covers the single-element form for an 8-byte element
  type beside the existing `int32` coverage.
