# Opening a borrowed byte composite with a quantified fact is refused

Soundness: incomplete. The kernel refuses an `open` whose body facts it
should reproduce; no false acceptance is known.

A composite that views `uint8` (or `char`) cells and states a quantified fact
about them, such as `forall (k) { 0 <= k and k < n implies p[k] != 0 }`,
cannot be opened by a function that borrows it: the kernel rejects the checked
resource step with "resource rewrite produced an unchecked pure-fact delta".
The same definition over `int32` cells opens and the proof verifies. The
Surface and the kernel evidently disagree on the form of a quantified byte
read (for example its promotion to `int32`), so a fact the Surface publishes
is not one the kernel's instantiation of the body produces.

`click verify --trace-proof` records no checked step for the failure, so the
trace does not show which fact differs.

## Reproduction

Found while prototyping a borrowed C-string resource (`cstr_at` in
`library/cstr.click` on branch `cstrview`), which states that no byte before
the terminator is `'\0'`.

```c filename=probe.c
uint8 first(uint8 p[], uint64 n) { return p[0]; }
```

```click
resource nonzero(p: uint8*, n: uint64) {
    views p[0..n];
    fact forall (k: uint64) { 0u64 <= k and k < n implies p[k] != 0 };
}

verifying "probe.c";

uint8 first(uint8 p[], uint64 n) {
    requires 0u64 < n;
    views nonzero(p, n);
    ensures true;
} by {
    open(nonzero(p, n)) {
        execute();
    }
}
```

Observed on master `5ad27faf`: `kernel rejected checked resource open:
resource rewrite produced an unchecked pure-fact delta`. Replacing every
`uint8` by `int32` verifies. A `char` element and an `int32` index fail the
same way as `uint8`.

## Acceptance

- The reproduction verifies as written, kept as an mdtest, with a `char`
  variant.
- The Surface and the kernel produce the same proposition for a quantified
  byte read in a composite body; the kernel's delta check is not weakened.
- When the delta check refuses, the diagnostic or trace names the fact it
  could not reproduce.
