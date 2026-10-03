# The `error` attribute is accepted only on a block-scope declaration

A file-scope declaration with the attribute stays rejected.

```c filename=c_error_attribute_file_scope_rejected.c
void fail(void) __attribute__((__error__("no")));

int32 run(int32 value) {
    return value;
}
```

```click
verifying "c_error_attribute_file_scope_rejected.c";

```

```expect
fail:c_error_attribute_file_scope_rejected.c:1: unsupported GNU function attribute `__error__`
```
