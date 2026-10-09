# A 64-bit bound must be shown to fit a 32-bit index

The contracts of `a_64_bit_index_and_bound_need_no_cast.md` without
`requires length <= 2147483647`. The range `bytes[0..length]` converts its
bound to the 32-bit index a place takes, and nothing shows the conversion is
exact, so the contract is refused when it is set up, with the requirement to
state.

```c filename=a_64_bit_bound_must_be_shown_to_fit_a_32_bit_index.c
unsigned char read(const unsigned char *bytes, unsigned long length, unsigned long index) {
    return bytes[index];
}
void write(unsigned char *bytes, unsigned long length, unsigned long index, unsigned char value) {
    bytes[index] = value;
}
```

```click
verifying "a_64_bit_bound_must_be_shown_to_fit_a_32_bit_index.c";
uint8 read(const uint8* bytes, uint64 length, uint64 index) {
    requires index < length;
    views bytes[0..length];
    ensures result == bytes[index];
} by { execute(); simp(); }
void write(uint8* bytes, uint64 length, uint64 index, uint8 value) {
    requires index < length;
    owns bytes[0..length];
    ensures bytes[index] == value;
} by { execute(); simp(); }
```

```expect
fail: a place takes a 32-bit index, so the contract has to state that this bound fits one
```
