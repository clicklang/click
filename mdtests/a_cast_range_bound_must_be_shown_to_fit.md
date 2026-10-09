# A cast range bound must be shown to fit

A range bound cast to `int32` is a 32-bit bound, and a contract that holds
the range has to show the cast loses nothing. Without
`requires length <= 2147483647` the contract is refused, and the refusal
says that the uncast range needs no such bound.

`a_cast_in_a_range_bound_truncates_the_bound.md` states the bound.

```c filename=a_cast_range_bound_must_be_shown_to_fit.c
unsigned char read(const unsigned char *bytes, unsigned long length, unsigned long index) {
    return bytes[index];
}
```

```click
verifying "a_cast_range_bound_must_be_shown_to_fit.c";
uint8 read(const uint8* bytes, uint64 length, uint64 index) {
    requires index < length;
    views bytes[0..(int32)length];
    ensures result == bytes[index];
} by { execute(); simp(); }
```

```expect
fail: written without a cast needs no such bound
```
