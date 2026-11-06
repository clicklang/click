# A pointer-valued pure call prints as an undefined pointer label

Soundness: diagnostic-only. The goal is checked as written. Only its printed
spelling is lost, and the printed form cannot be written back.

A goal that compares the result of a pure function returning a pointer
prints that result as `<pointer A>`, and the report defines no such label. So
the goal cannot be written back into a proof, which breaks the rule that
every printed fact is spellable. The same happens to a read through such a
pointer: a slice element `s[i]` of a slice value whose data is
`slice::as_ptr(s)` prints as `old(*<pointer A>)`.

## Reproduction

A C unit with `f.c`:

```c
unsigned char first(const unsigned char *p, unsigned long n)
{
	return p[0];
}
```

```click
verifying "f.c";

function opaque_first(p: uint8*, n: uint64) -> uint8* {
    p
}

uint8 first(const uint8* p, uint64 n) {
    requires 1u64 <= n;
    requires n <= 4096u64;
    views p[0..n];
    ensures result == p[0];
} by {
    have opaque_first(p, n) == p + 1;
    step_until(function.exit);
    solve();
}
```

The refusal prints `could not establish \`opaque_first(p, n) == (p + 1)\``,
which is correct, then `goal: <pointer A> == &p[1]` with no legend entry for
`<pointer A>`.

In a Rust sidecar with a slice-valued pure function `half(bytes)`, the
failing `have half(bytes).as_ptr() == bytes + 1` prints
`goal: <pointer A> == &bytes[1]`, and `have half(bytes)[1] == 7u8` prints
`goal: match half(old(bytes)) { Slice(_, _) => old(*<pointer A>) } == 7`.

## Acceptance criteria

- The C reproduction's goal prints `opaque_first(p, n) == &p[1]`, or a
  `<pointer A>` with a legend line naming `opaque_first(p, n)`.
- In the Rust case, the goals print `half(old(bytes)).as_ptr() == &bytes[1]`
  and `half(old(bytes))[1] == 7`.
- An mdtest pins each printed goal.
