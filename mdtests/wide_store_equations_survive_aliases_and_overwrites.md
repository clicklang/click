# Wide store equations survive aliases and overwrites

Signed and unsigned 64-bit stores publish their value at the store's program
point. Address aliases preserve that equation, and overwrites keep the old
point's value distinct.

```c filename=put.c
void put_u(uint64* p, uint64* q) {
    *p = 0xfedcba9876543210ULL;
    *p = 9;
}
void put_i(int64* p, int64* q) {
    *p = -7;
    *p = 9;
}
```

```click
verifying "put.c";
void put_u(uint64* p, uint64* q) {
    requires p == q;
    owns p[0..1];
    ensures *p == 9;
} by {
    step();
    mark first;
    have *p == 18364758544493064720 as uint64 by { close(); }
    have *q == 18364758544493064720 as uint64 by { rewrite(q, p); close(); }
    step();
    have *p == 9 by { close(); }
    have at(first, *p) == 18364758544493064720 as uint64 by { close(); }
}
void put_i(int64* p, int64* q) {
    requires p == q;
    owns p[0..1];
    ensures *p == 9;
} by {
    step();
    mark first;
    have *p == -7 by { close(); }
    have *q == -7 by { rewrite(q, p); close(); }
    step();
    have *p == 9 by { close(); }
    have at(first, *p) == -7 by { close(); }
}
```

```expect
pass
```
