# Observing a wildcard sum requires a representable total

Two individually valid counts do not justify a wildcard sum without a bound.

```c filename=counted_distinct_populations_symbolic_sum.c
int identity(void *p, void *q, int n) { return n; }
```

```click
verifying "counted_distinct_populations_symbolic_sum.c";
abstract resource ticket(p: void*);
int32 identity(void* p, void* q, int32 n) {
    owns ticket(p);
    owns ticket(q);
    requires p != q;
    requires count(ticket(p)) == n;
    requires count(ticket(q)) == 1;
    requires n >= 1;
    ensures result == n;
} by {
    have count(ticket(_)) >= 0 by { simp(); }
    execute(); simp();
}
```

```expect
fail: int32 overflow(value A + value B) is false
```
