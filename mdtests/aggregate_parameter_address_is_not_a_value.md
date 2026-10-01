# Explicit address-taking cannot read a retained logical parameter value

`*(&input.value)` reads one byte at the parameter's address, and the store
that wrote the four-byte field is not that byte's value: a load term carries
the width and signedness of its read, so the claim is refused at the proof.
It used to be refused only at contract certification, after a proof that took
the four-byte store as the byte read's value.

```c filename=aggregate_parameter_address_is_not_a_value.c
struct packet { int32 value; };
int32 read_value(struct packet input) { return input.value; }
```

```click
verifying "aggregate_parameter_address_is_not_a_value.c";
int32 read_value(struct packet input) {
    ensures result == *(&input.value);
} by { execute(); simp(); }
```

```expect
fail: `ensures result == *byte_offset(input, 0)` failed for `read_value.ensures_0`
```
