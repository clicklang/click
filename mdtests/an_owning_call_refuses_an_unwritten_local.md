# An owning call refuses an unwritten local

`get` views `p[0..1]`, a plain clause: its proof starts with `*p`
initialized and reads it. A caller must therefore have initialized every
byte it passes. `caller` passes a local no one has written, so the call is
refused. A callee that writes the range before reading it owns
`uninitialized(p[0..1])` instead
([`owns_uninitialized_reads_what_it_wrote.md`](owns_uninitialized_reads_what_it_wrote.md)).

```c filename=get_unwritten.c
int get(const int *p) { return *p; }

int caller(void)
{
	int x;
	return get(&x);
}
```

```click
verifying "get_unwritten.c";

int32 get(const int32* p) {
    views p[0..1];
    ensures result == p[0];
}

int32 caller() {
    ensures true;
}
```

```expect
fail: resource clause 1 of 1 holds its range as initialized, but the caller has not initialized every byte of it
```
