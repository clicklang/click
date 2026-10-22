# A local no callee owned is still uninitialized

The negative of
[`a_local_lent_to_an_owning_callee_is_initialized_after_the_call.md`](a_local_lent_to_an_owning_callee_is_initialized_after_the_call.md).
`peek` only views `a`, so it writes nothing, and reading `a[1]` afterwards
reads a byte no one wrote: undefined behavior, as without the call.

```c filename=unlent_local.c
int peek(int *a) { return 0; }

int peeked(void)
{
	int a[3];
	a[0] = 5;
	peek(a);
	return a[1];
}
```

```click
verifying "unlent_local.c";

int32 peek(int32 a[]) {
    views a[0..1];
    ensures result == 0;
} by { execute(); simp(); }

int32 peeked() {
    ensures true;
} by { execute(); simp(); }
```

```expect
fail: read of uninitialized storage
```
