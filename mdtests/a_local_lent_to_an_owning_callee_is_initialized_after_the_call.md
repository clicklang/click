# A callee that ensures `defined` initializes the caller's local

A local array's frame owns its bytes, as a declared scalar's does, so a
function can pass the array to a callee that owns its buffer: `fill(a)`
below, and Linux `string_get_size`'s `snprintf(tmp, sizeof(tmp), ".%03u",
remainder)`.

Each callee here writes memory no one has written, so it owns it as
`uninitialized(...)`. Owning memory lets a callee write it but does not say
it did. A callee that writes caller memory states which bytes it initialized with `ensures
defined(...)`, which its own proof checks against its body; after the call the
caller may read those bytes, whether the local is an array (`a[0]` after
`fill(a)`) or a scalar whose address was passed (`x` after `set(&x)`). The
generated `snprintf` contract states `defined` for every character it writes.

Without that postcondition the bytes stay unwritten for the caller: see
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
    owns uninitialized(a[0..1]);
    ensures defined(a[0]);
    ensures a[0] == 1;
} by { execute(); simp(); }

int32 filled() {
    ensures result == 1;
} by { execute(); simp(); }

void set(int32* p) {
    owns uninitialized(p[0..1]);
    ensures defined(p[0]);
    ensures p[0] == 1;
} by { execute(); simp(); }

int32 was_set() {
    ensures result == 1;
} by { execute(); simp(); }
```

```expect
pass
```
