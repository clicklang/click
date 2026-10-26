# An initializer produces the memory it initialized

`init` consumes `uninitialized(p[0..1])` and produces `p[0..1]`: it takes
storage no one has written and returns it initialized. Its proof checks that
every byte it produces is written. After the call the caller holds `x`
initialized, so it may read it and pass it to `bump`, which owns it plain.
The negative case is
[`produces_refuses_memory_the_function_did_not_write.md`](produces_refuses_memory_the_function_did_not_write.md).

```c filename=initializer.c
void init(int *p) { *p = 1; }

void bump(int *p) { *p = *p + 1; }

int caller(void)
{
	int x;
	init(&x);
	bump(&x);
	return x;
}
```

```click
verifying "initializer.c";

void init(int32* p) {
    consumes uninitialized(p[0..1]);
    produces p[0..1];
    ensures p[0] == 1;
}

void bump(int32* p) {
    owns p[0..1];
    requires p[0] < 2147483647;
    ensures p[0] == old(p[0]) + 1;
}

int32 caller() {
    ensures result == 2;
}
```

```expect
pass
```
