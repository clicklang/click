# A zero operand still requires a valid count

```c filename=shift.c
int32 shift32(int32 count) { return 0 << count; }
```

```click
verifying "shift.c";

int32 shift32(int32 count) {
    requires count == 32;
    ensures true;
}
```

```expect
fail: invalid shift
```
