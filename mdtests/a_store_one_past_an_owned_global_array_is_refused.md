# a store one past an owned global array is refused

`j <= 1000` admits `j == 1000`, one element past `buf[0..1000]`, so the store
may land outside the owned footprint and must be refused. The refusal spells
the store in source terms rather than as a kernel pointer.

```c filename=a_store_one_past_an_owned_global_array_is_refused.c
int32 buf[1001];

void set_upper(int32 j) {
    buf[j] = 5;
}
```

```click
verifying "a_store_one_past_an_owned_global_array_is_refused.c";

void set_upper(int32 j) {
    owns buf[0..1000];
    requires 500 <= j and j <= 1000;
    ensures buf[j] == 5 by auto;
}
```

```expect
fail: write to storage outside the owned footprint: the 4-byte store to `(char *)&buf + j * 4`; own the written cells or declare them in a `mutable` clause
```
