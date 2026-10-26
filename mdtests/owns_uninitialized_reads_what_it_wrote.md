# `owns uninitialized(...)` reads what it wrote

`set_then_get` owns `uninitialized(p[0..1])`: its caller may pass storage no
one has written. The callee writes `*p` before it reads it, so the read is
defined, and it states what it initialized with `ensures defined(p[0])`.
The caller lends a fresh local and reads it after the call on that ensures
alone. The negative case is
[`owns_uninitialized_refuses_a_read_before_a_write.md`](owns_uninitialized_refuses_a_read_before_a_write.md).

```c filename=uninitialized_set_then_get.c
int set_then_get(int *p) { *p = 1; return *p; }

int caller(void)
{
	int x;
	int y = set_then_get(&x);
	return x + y;
}
```

```click
verifying "uninitialized_set_then_get.c";

int32 set_then_get(int32* p) {
    owns uninitialized(p[0..1]);
    ensures result == 1;
    ensures p[0] == 1;
    ensures defined(p[0]);
}

int32 caller() {
    ensures result == 2;
}
```

```expect
pass
```
