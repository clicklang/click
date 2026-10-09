# A cast in a place reads the truncated index

`bytes[(int32)index]` is legal and means what it says: the element at the
index truncated to 32 bits. The C reads `bytes[index]`, at the 64-bit
index. The two are the same element only when the index fits 32 bits, and
that is not assumed, so a contract that names the cast place does not
describe what the function returns.

Write the index as the C has it, as `uint64_index_variable_length.md` does.

```c filename=a_cast_in_a_place_reads_the_truncated_index.c
unsigned char read(const unsigned char *bytes, unsigned long length, unsigned long index) {
    return bytes[index];
}
```

```click
verifying "a_cast_in_a_place_reads_the_truncated_index.c";
uint8 read(const uint8* bytes, uint64 length, uint64 index) {
    requires index < length;
    views bytes[0..length];
    ensures result == bytes[(int32)index];
} by { execute(); simp(); }
```

```expect
fail: read the same recorded memory using different address expressions
```
