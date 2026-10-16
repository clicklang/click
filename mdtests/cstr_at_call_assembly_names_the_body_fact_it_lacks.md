# A refused call-site assembly names the body fact it lacks

[`cstr_readable_witness_stated_before_call.md`](cstr_readable_witness_stated_before_call.md)
without its three `have`s. The entry facts state each byte of `bytes`
separately, but `cstr_at(bytes, 2u64)`'s body states the nonzero bytes as one
quantified fact. Assembling the view `strlen` requires from the owned bytes
is a fold, so the refusal names the assembled instance and the first body
fact the caller has not established, beside the facts it has.

```c filename=cstr_at_call_assembly_names_the_body_fact_it_lacks.c
uint64 fixed_string_length(uint8 bytes[]) {
    uint64 length;
    length = strlen(bytes);
    return length;
}
```

```click
verifying "cstr_at_call_assembly_names_the_body_fact_it_lacks.c";

uint64 fixed_string_length(uint8 bytes[]) {
    owns bytes[0..3];
    requires bytes[0] != '\0';
    requires bytes[1] != '\0';
    requires bytes[2] == '\0';
    ensures result == 2u64;
} by {
    execute_until(statement(1));
    step(strlen(bytes), { s: click::cstr::cstr_at(bytes, 2u64) });
    execute();
    simp();
}
```

```expect
fail: assembling `views cstr_at(bytes, 2u64)` from owned pieces requires an exact body fact: missing pure fact: forall (k: uint64) { true and k < 2u64 implies
```
