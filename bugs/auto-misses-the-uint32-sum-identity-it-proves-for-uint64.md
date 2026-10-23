# `auto` misses the `uint32` sum identity it proves for `uint64`

Soundness: incomplete. A provable goal is refused; nothing false verifies.

## Violated invariant

A rule stated over a machine format holds at every format
(`design/machine-integers.md`). `auto` proves an in-range machine `+` equal
to its Integer sum from the Integer bound of that sum for `uint64`, but not
for `uint32`:

```click
theorem uint32_sum_identity(a: uint32, b: uint32) {
    requires to_integer(a) + to_integer(b) <= 4294967295;
    ensures to_integer(a + b) == to_integer(a) + to_integer(b) by auto();
}
```

`auto` refuses: "could not establish `to_integer((a + b)) == (to_integer(a)
+ to_integer(b))`". The same theorem over `uint64`, with bound
`18446744073709551615`, verifies. The `uint32` theorem verifies when each
operand has its own constant bound (`a <= 100u32`).

Proofs cite `click::integer::uint32_add_to_integer` for this instead: about
115 sites in `design/adler32/project/adler2`.

## Reproduction

Save the theorem above as `u32.click` and run `click verify u32.click`.

## Acceptance

- The reproduction verifies, and a `uint32` regression sits beside the
  `uint64` one.
- The `uint32_add_to_integer` citations it replaces are removed.
