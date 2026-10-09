# A separation from a 64-bit range does not make a false claim true

The contract of `a_separation_from_a_64_bit_range.md` claiming the result
is the value written through `value`. The read is of `bytes[index]`, which
the separation says the write did not touch, so the claim is refused.

```c filename=a_separation_from_a_64_bit_range_does_not_make_a_false_claim_true.c
unsigned char set_and_read(int *value, const unsigned char *bytes, unsigned long length, unsigned long index) {
    *value = 7;
    return bytes[index];
}
```

```click
verifying "a_separation_from_a_64_bit_range_does_not_make_a_false_claim_true.c";
uint8 set_and_read(int32* value, const uint8* bytes, uint64 length, uint64 index) {
    requires index < length;
    requires separate(memory(value[0..1]), memory(bytes[0..length]));
    owns value[0..1];
    views bytes[0..length];
    ensures result == 7;
} by { execute(); simp(); }
```

```expect
fail: result == 7
```
