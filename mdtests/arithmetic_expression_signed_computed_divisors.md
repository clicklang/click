# Signed division checks the relevant bitwise property of the divisor

```c filename=arithmetic.c
int32 divide_or(int32 n, int32 k) { return n / (k | 1); }
int64 remain_or(int64 n, int64 k) { return n % (1LL | k); }
int32 divide_xor(int32 n, int32 k) { return n / (k ^ 1); }
int64 remain_xor(int64 n, int64 k) { return n % (1LL ^ k); }
```

```click
verifying "arithmetic.c";

int32 divide_or(int32 n, int32 k) { requires k >= 0; ensures true; }
int64 remain_or(int64 n, int64 k) { requires k >= 0i64; ensures true; }
int32 divide_xor(int32 n, int32 k) {
    requires k != 1;
    requires n != (-2147483647 - 1);
    ensures true;
}
int64 remain_xor(int64 n, int64 k) {
    requires k != 1i64;
    requires n != (-9223372036854775807i64 - 1i64);
    ensures true;
}
```

```expect
pass
```
