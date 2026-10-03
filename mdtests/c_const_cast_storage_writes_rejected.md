# A cast that drops `const` does not make const storage writable

An explicit cast may drop `const`, as in C, but writing a const object
through the resulting pointer is undefined behaviour. Click rejects the
store because the storage itself is read-only, whatever the pointer says.
This file checks a const scalar global; the companion files check a table,
an aggregate, a function-local `static const` object, a string literal, and
a write made by a callee.

```c filename=c_const_cast_storage_writes_rejected.c
const int limit = 3;

int32 run(void) {
    int *p = (int *)&limit;
    *p = 4;
    return limit;
}
```

```click
verifying "c_const_cast_storage_writes_rejected.c";

int32 run() {
    ensures result == result by auto;
}
```

```expect
fail: invalid memory access
```
