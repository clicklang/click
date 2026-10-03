# A byte at its maximum cannot increment within the byte bound

```c filename=bounded_byte_increment_fail.c
long next(unsigned char byte) {
    unsigned word = (unsigned)byte;
    return (long)word + 1;
}
```

```click
verifying "bounded_byte_increment_fail.c";
int64 next(uint8 byte) {
    requires byte == 255;
    ensures result <= 255i64;
} by { execute(); simp(); }
```

```expect
fail: unclosed goal
```
