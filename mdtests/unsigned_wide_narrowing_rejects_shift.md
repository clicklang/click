# Six extracted bits do not fit a 32-bit shift count

```c filename=shift.c
unsigned int shift(unsigned long x) { unsigned int n = x >> 58; return 1u << n; }
```

```click
verifying "shift.c";
unsigned int shift(unsigned long x) {
    ensures result == result;
}
```

```expect
fail: invalid shift
```
