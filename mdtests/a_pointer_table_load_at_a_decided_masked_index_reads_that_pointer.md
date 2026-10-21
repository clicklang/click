# A pointer-table load at a decided masked index reads that pointer

With the index decided, the load reads the selected object alone.

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
    requires (u & 1) == 1;
    ensures result == 6;
} by {
    execute();
    simp();
}
```

```expect
pass
```
