# Excluding the sole overflowing operand

Negation is safe when its operand differs from `INT_MIN`. Division also
excludes its only overflowing pair when either operand differs from that pair.

```c filename=single_overflow.c
int32 negate(int32 x) { return -x; }
int32 negate_ordered(int32 x) { return -x; }
int32 negate_mirrored(int32 x) { return -x; }
int32 divide_left(int32 x, int32 y) { return x / y; }
int32 divide_right(int32 x, int32 y) { return x / y; }
int32 remainder_left(int32 x, int32 y) { return x % y; }
int32 remainder_right(int32 x, int32 y) { return x % y; }
```

```click
verifying "single_overflow.c";
int32 negate(int32 x) {
    requires x != -2147483647 - 1;
    ensures result == -x;
} by { execute(); simp(); }
int32 negate_ordered(int32 x) {
    requires x > -2147483647 - 1;
    ensures result == -x;
} by { execute(); simp(); }
int32 negate_mirrored(int32 x) {
    requires -2147483647 - 1 != x;
    ensures result == -x;
} by { execute(); simp(); }
int32 divide_left(int32 x, int32 y) {
    requires y != 0;
    requires x != -2147483647 - 1;
    ensures result == x / y;
} by { execute(); simp(); }
int32 divide_right(int32 x, int32 y) {
    requires y != 0;
    requires y != -1;
    ensures result == x / y;
} by { execute(); simp(); }
int32 remainder_left(int32 x, int32 y) {
    requires y != 0;
    requires x != -2147483647 - 1;
    ensures result == x % y;
} by { execute(); simp(); }
int32 remainder_right(int32 x, int32 y) {
    requires y != 0;
    requires y != -1;
    ensures result == x % y;
} by { execute(); simp(); }
```

```expect
pass
```
