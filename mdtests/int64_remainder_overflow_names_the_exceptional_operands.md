# Signed 64-bit remainder names the operand pair that overflows

```c filename=remainder.c
int64 remainder_overflow() {
    return (-9223372036854775807LL - 1) % -1;
}
```

```click
verifying "remainder.c";

int64 remainder_overflow() {
    ensures true;
}
```

```expect
fail: signed overflow (the minimum signed 64-bit value divided by -1 overflows division and remainder)
```
