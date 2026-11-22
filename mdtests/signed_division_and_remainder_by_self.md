# A nonzero signed value can divide itself or take its own remainder

```c filename=divide.c
int32 divide32(int32 x) { return x / x; }
int32 remainder32(int32 x) { return x % x; }
int64 divide64(int64 x) { return x / x; }
int64 remainder64(int64 x) { return x % x; }
```

```click
verifying "divide.c";

int32 divide32(int32 x) {
    requires x != 0;
    ensures true;
}

int32 remainder32(int32 x) {
    requires x != 0;
    ensures true;
}

int64 divide64(int64 x) {
    requires x != 0i64;
    ensures true;
}

int64 remainder64(int64 x) {
    requires x != 0i64;
    ensures true;
}
```

```expect
pass
```
