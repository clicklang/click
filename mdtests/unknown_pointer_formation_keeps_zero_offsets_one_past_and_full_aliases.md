# Unknown pointer formation keeps zero offsets, one-past and full aliases

Zero displacement needs no additional bounds. A held range permits its
one-past endpoint, and complete pointer equality transfers bounds evidence.

```c filename=formation.c
int32* zero(int32* p, int32 n) { return p + n; }
int32* signed_zero(int32* p, int64 n) { return p + n; }
int32* unsigned_zero(int32* p, uint64 n) { return p - n; }
int32* one_past(int32* p) { return p + 2; }
int32* alias(int32* p, int32* q) { return p + 1; }
```

```click
verifying "formation.c";
int32* zero(int32* p, int32 n) {
    requires n == 0;
    ensures result == p;
} by { execute(); simp(); }
int32* signed_zero(int32* p, int64 n) {
    requires n == 0i64;
    ensures result == p;
} by { execute(); simp(); }
int32* unsigned_zero(int32* p, uint64 n) {
    requires n == 0u64;
    ensures result == p;
} by { execute(); simp(); }
int32* one_past(int32* p) {
    views p[0..2];
    ensures result == p + 2;
} by { execute(); simp(); }
int32* alias(int32* p, int32* q) {
    views q[0..2];
    requires p == q;
    ensures result == q + 1;
} by { execute(); simp(); }
```

```expect
pass
```
