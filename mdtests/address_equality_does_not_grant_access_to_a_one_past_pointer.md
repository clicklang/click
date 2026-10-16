# Address equality does not grant access to a one-past pointer

A callee may read `*q` only through authority `q` itself carries. `q == p`
says the addresses are equal, not that `q` designates the object `p` does:
`q` may be one past `first` while `p` is `&second`, or one past an array
while `p` points to another object placed after it. Reading through `q` is
then undefined, so the comparison grants `q` none of `p`'s authority.

```c filename=compare.c
int32 cmp(int32* q, int32* p) { if (q == p) { return *q; } return 0; }
```

```click
verifying "compare.c";
int32 cmp(int32* q, int32* p) {
    views p[0..1];
    ensures 1 == 1;
} by { execute(); simp(); }
```

```expect
fail: missing resource fact `views q[0]`
```
