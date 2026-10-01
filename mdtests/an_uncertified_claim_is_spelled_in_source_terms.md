# An uncertified contract claim is spelled in source terms

When `by auto` proves a claim that exact symbolic execution then does not
certify, the refusal names the claim by its label and spells its clause in source terms,
not as a dump of the kernel's internal proposition.

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
fail: unverified claims: read_value.ensures_0 `result == *byte_offset(input, 0)`
```
