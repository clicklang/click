# A local lent to an owning callee is initialized after the call

A local array's frame owns its bytes, as a declared scalar's does, so a
function can pass the array to a callee that owns its buffer: `fill(a)`
below, and Linux `string_get_size`'s `snprintf(tmp, sizeof(tmp), ".%03u",
remainder)`.

Inside a callee, memory its caller lends reads as initialized; the caller
cannot tell which of those bytes the callee wrote. So when a call may write
part of a caller's local, that part is initialized after it returns, and the
caller may read it: `a[0]` after `fill(a)`, and `x` after `set(&x)`. What the
callee's postcondition states is what the caller knows of the values.

Reading what no one could have written is still undefined behavior: see
[`a_local_no_callee_owned_is_still_uninitialized.md`](a_local_no_callee_owned_is_still_uninitialized.md).

```c filename=lent_local.c
void fill(int *a) { a[0] = 1; }

int filled(void)
{
	int a[3];
	fill(a);
	return a[0];
}

void set(int *p) { *p = 1; }

int was_set(void)
{
	int x;
	set(&x);
	return x;
}
```

```click
verifying "lent_local.c";

void fill(int32 a[]) {
    owns a[0..1];
    ensures a[0] == 1;
} by { execute(); simp(); }

int32 filled() {
    ensures result == 1;
} by { execute(); simp(); }

void set(int32* p) {
    owns p[0..1];
    ensures p[0] == 1;
} by { execute(); simp(); }

int32 was_set() {
    ensures result == 1;
} by { execute(); simp(); }
```

```expect
pass
```
