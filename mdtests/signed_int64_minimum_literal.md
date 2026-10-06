# A typed signed 64-bit minimum literal

Only unary minus admits the one extra magnitude. The literal remains a native
int64 value, and its mathematical observation is exact.

```click
theorem minimum() {
    ensures to_integer(-9223372036854775808i64) == -9223372036854775808 by { normalize(); }
}
```

```expect
pass
```
