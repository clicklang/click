# A pointer-table load at a masked index is one of its pointers

A function-scope `static` table of object pointers indexed by `u & 1` reads
one of its two stored pointers, so indexing through it is defined. `u & 1`
lies in `0..=1`, and the case split off the second cell leaves the index on
the first.

```c filename=k1.c
static const int a[2] = { 3, 4 };
static const int b[2] = { 5, 6 };
int f(unsigned int u)
{
	static const int *const t[] = { &a[0], &b[0] };
	return t[u & 1][1];
}
```

```click
verifying "k1.c";
int32 f(uint32 u) {
    ensures result == 4 or result == 6;
} by {
    execute();
    simp();
}
```

```expect
pass
```
