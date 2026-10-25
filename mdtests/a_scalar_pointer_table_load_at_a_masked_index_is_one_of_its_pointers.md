# A scalar pointer-table load at a masked index is one of its pointers

The scalar form `*t[u & 1]` of a table of `&a` and `&b` dereferences one of
the two stored pointers, not an offset into the table itself.

```c filename=k2.c
static const int a = 3;
static const int b = 5;
int f(unsigned int u)
{
	static const int *const t[] = { &a, &b };
	return *t[u & 1];
}
```

```click
verifying "k2.c";
int32 f(uint32 u) {
    ensures result == 3 or result == 5;
}
```

```expect
pass
```
