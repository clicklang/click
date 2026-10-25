# `produces uninitialized(...)` reaches the caller unwritten

`make` is a trusted allocator: it produces `uninitialized(result[0..1])`,
bytes the caller owns with no claim that they are initialized, as fresh
`malloc` storage is. Reading `*q` before writing it is a read of
uninitialized storage. Writing first, as `make_one` does, is defined.

```c filename=uninitialized_produce.c
int *make(void);

int read_fresh(void)
{
	int *q = make();
	return *q;
}

int make_one(void)
{
	int *q = make();
	*q = 1;
	return *q;
}
```

```click
verifying "uninitialized_produce.c";

extern int32* make() {
    produces uninitialized(result[0..1]);
}

int32 make_one() {
    ensures result == 1;
} by { execute(); solve(); }

int32 read_fresh() {
    ensures true;
} by { execute(); solve(); }
```

```expect
fail: read of uninitialized storage
```
