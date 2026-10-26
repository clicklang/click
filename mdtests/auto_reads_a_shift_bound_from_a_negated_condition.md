# The implicit closer reads a shift bound from a negated condition

The else arm of a proof `if (b >> 32) != 0u64` holds `not ((b >> 32) != 0u64)`.
The implicit closer reads it as `to_integer(b >> 32) == 0` and bounds the shift by its
operand, `to_integer(b) <= 4294967296 * to_integer(b >> 32) + 4294967295`,
so `b < 4294967296u64` follows. The certificate spells the shift from the
negated comparison's own operands, as it spells one from a comparison.

```c filename=auto_reads_a_shift_bound_from_a_negated_condition.c
unsigned long g(unsigned long b)
{
	if (b >> 32)
		return 0;
	return b;
}
```

```click
verifying "auto_reads_a_shift_bound_from_a_negated_condition.c";

uint64 g(uint64 b) {
    ensures result < 4294967296u64;
} by {
    if (b >> 32) != 0u64 {
        execute();
        solve();
    } else {
        have b < 4294967296u64;
        execute();
        solve();
    }
}
```

```expect
pass
```
