# A separation from a 64-bit range

`separate(...)` names a range with the same reading a contract clause
gives it: `memory(bytes[0..length])` with a `size_t` length is the range
with 64-bit bounds that `views bytes[0..length]` holds. The write through
`value` then leaves `bytes[index]` as it was, because the two are stated
separate.

The requirement is redundant here, since an owned and a viewed input are
separate already; it is stated to pin that a separation over a wide range
lowers, which it did not.

`a_separation_from_a_64_bit_range_does_not_make_a_false_claim_true.md`
claims the written value came back.

```c filename=a_separation_from_a_64_bit_range.c
unsigned char set_and_read(int *value, const unsigned char *bytes, unsigned long length, unsigned long index) {
    *value = 7;
    return bytes[index];
}
```

```click
verifying "a_separation_from_a_64_bit_range.c";
uint8 set_and_read(int32* value, const uint8* bytes, uint64 length, uint64 index) {
    requires index < length;
    requires separate(memory(value[0..1]), memory(bytes[0..length]));
    owns value[0..1];
    views bytes[0..length];
    ensures result == old(bytes[index]);
    ensures value[0] == 7;
} by { execute(); simp(); }
```

```expect
pass
```
