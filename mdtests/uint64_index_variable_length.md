# A uint64 index below a bounded variable length accesses the same byte

The index and length retain their 64-bit identities. Only a proved upper
bound below the signed-word limit permits the memory range's word indices.

```c filename=uint64_index_variable_length.c
unsigned char read(const unsigned char *bytes, unsigned long length, unsigned long index) {
    return bytes[index];
}
void write(unsigned char *bytes, unsigned long length, unsigned long index, unsigned char value) {
    bytes[index] = value;
}
```

```click
verifying "uint64_index_variable_length.c";
uint8 read(const uint8* bytes, uint64 length, uint64 index) {
    requires length <= 2147483647u64;
    requires index < length;
    views bytes[0..(int32)length];
    ensures result == bytes[(int32)index];
} by { execute(); simp(); }
void write(uint8* bytes, uint64 length, uint64 index, uint8 value) {
    requires length <= 2147483647u64;
    requires index < length;
    owns bytes[0..(int32)length];
    ensures bytes[(int32)index] == value;
} by { execute(); simp(); }
```

```expect
pass
```
