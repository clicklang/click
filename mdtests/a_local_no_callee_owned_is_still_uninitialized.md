# A local no callee states `defined` is still uninitialized

The negative of
[`a_local_lent_to_an_owning_callee_is_initialized_after_the_call.md`](a_local_lent_to_an_owning_callee_is_initialized_after_the_call.md).
`nop` owns `uninitialized(p[0..1])`, so it could write `x`, but it does not,
and its contract states nothing about `x`. Ownership alone does not certify initialization, so
reading `x` after the call reads a byte no one wrote: undefined behavior.

```c filename=unlent_local.c
void nop(int *p) { }

int after_nop(void)
{
	int x;
	nop(&x);
	return x;
}
```

```click
verifying "unlent_local.c";

void nop(int32* p) {
    owns uninitialized(p[0..1]);
    ensures true;
} by { execute(); simp(); }

int32 after_nop() {
    ensures true;
} by { execute(); simp(); }
```

```expect
fail: read of uninitialized storage
```
