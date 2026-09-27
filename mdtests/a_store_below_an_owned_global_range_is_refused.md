# a store below an owned global range is refused

The contract owns `buf[1..1000]`, and `0 <= j` admits `j == 0`, the element
just below it. The store is inside the C array, so it is defined, but it may
land outside the owned footprint: the upper bound alone does not place it
inside.

```c filename=a_store_below_an_owned_global_range_is_refused.c
int32 buf[1000];

void set_upper(int32 j) {
    buf[j] = 5;
}
```

```click
verifying "a_store_below_an_owned_global_range_is_refused.c";

void set_upper(int32 j) {
    owns buf[1..1000];
    requires 0 <= j and j < 1000;
    ensures buf[j] == 5 by auto;
}
```

```expect
fail: write to storage outside the owned footprint: the 4-byte store to `(char *)&buf + j * 4`
```
