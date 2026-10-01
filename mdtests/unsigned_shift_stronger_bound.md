# A stronger unsigned count bound rules out an invalid shift

`count < 8` implies `count < 32`. The execution checker must refute the
invalid-shift branch through the indexed upper bound, without requiring the
contract to restate the weaker bound.

```c filename=unsigned_shift_stronger_bound.c
unsigned shift(unsigned value, unsigned count) {
    return value << count;
}
```

```click
verifying "unsigned_shift_stronger_bound.c";
uint32 shift(uint32 value, uint32 count) {
    requires count < 8u32;
    ensures result == (value << count);
} by { execute(); simp(); }
```

```expect
pass
```
