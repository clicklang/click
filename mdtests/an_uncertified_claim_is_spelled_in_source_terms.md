# An uncertified contract claim is spelled in source terms

When a claim is refused, the refusal names the claim by its label and spells
its clause in source terms, not as a dump of the kernel's internal
proposition.

The explicit `load_uint8` asks for a byte read beside the int32 field read.
Taking an int32 field's address preserves its pointee type; spelling the byte
read explicitly keeps these two read interpretations distinct. The verifier
must refuse an unsupported equality between them and name the source claim.
`c_step_contract_no_double_ownership.md` separately pins certification refusals.

```c filename=an_uncertified_claim_is_spelled_in_source_terms.c
struct packet { int32 value; };
int32 read_value(struct packet input) { return input.value; }
```

```click
verifying "an_uncertified_claim_is_spelled_in_source_terms.c";
int32 read_value(struct packet input) {
    ensures result == load_uint8(byte_offset(input, 0)) by auto;
}
```

```expect
fail: `ensures result == load_uint8(byte_offset(input, 0))` failed for `read_value.ensures_0`
```
