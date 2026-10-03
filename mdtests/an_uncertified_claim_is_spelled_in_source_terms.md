# An uncertified contract claim is spelled in source terms

When a claim is refused, the refusal names the claim by its label and spells
its clause in source terms, not as a dump of the kernel's internal
proposition.

This file used to reach that refusal one step later, at contract
certification: `by auto` proved the claim and exact symbolic execution then
did not certify it. The proof was wrong. `*(&input.value)` reads one byte at
the parameter's address (`load(input)u8` below), and `input.value` reads four,
yet the two reads shared one load term, so the store that wrote the four-byte
field supplied the byte read as well. A load term now carries the width and
signedness of its read, the store no longer supplies a narrower read, and the
proof itself refuses. `c_step_contract_no_double_ownership.md` still pins the
certification refusal, spelled the same way.

```c filename=an_uncertified_claim_is_spelled_in_source_terms.c
struct packet { int32 value; };
int32 read_value(struct packet input) { return input.value; }
```

```click
verifying "an_uncertified_claim_is_spelled_in_source_terms.c";
int32 read_value(struct packet input) {
    ensures result == *(&input.value) by auto;
}
```

```expect
fail: `ensures result == *byte_offset(input, 0)` failed for `read_value.ensures_0`
```
