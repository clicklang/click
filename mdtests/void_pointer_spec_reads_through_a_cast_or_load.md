# A spec reads through a `void *` by naming the type

A `void *` states no pointee type, so a spec names one: it casts to a typed
pointer, or reads with `load<T>`.

```c filename=void_pointer_spec_reads_through_a_cast_or_load.c
uint8 first(void *q) {
    return *(uint8 *)q;
}

uint8 also_first(void *q) {
    return *(uint8 *)q;
}
```

```click
verifying "void_pointer_spec_reads_through_a_cast_or_load.c";

uint8 first(void *q) {
    views (q as (uint8 *))[0..1];
    ensures result == *(q as (uint8 *));
}

uint8 also_first(void *q) {
    views (q as (uint8 *))[0..1];
    ensures result == load<uint8>(q);
}
```

```expect
pass
```
