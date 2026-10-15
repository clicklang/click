# A contract value equality carries pointer designation

```c filename=probe.c
int32 read_equal(int32* q, int32* p) {
    if (q == p) { return *q; }
    return 0;
}
```

```click
verifying "probe.c";
int32 read_equal(int32* q, int32* p) {
    requires q == p;
    views p[0..1];
    ensures result == p[0];
} by { execute(); simp(); }
```

```expect
pass
```
