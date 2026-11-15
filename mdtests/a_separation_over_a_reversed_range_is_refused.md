# Separation may name a reversed range without granting access

The endpoints make a reversed range whose wrapped difference is two. Naming
it in separation adds no extent fact or access permission. The independent
ownership clause authorizes the read of `b[0]`.

```c filename=a_separation_over_a_reversed_range_is_refused.c
int32 separate_over_reversed_range(int32 a[], int32 b[], int32 s, int32 t) {
    return b[0];
}
```

```click
verifying "a_separation_over_a_reversed_range_is_refused.c";

int32 separate_over_reversed_range(int32 a[], int32 b[], int32 s, int32 t) {
    requires s == 2147483647;
    requires t == -2147483647;
    requires separate(memory(a[s..t]), memory(b[0..1]));
    owns b[0..1];

    ensures result == b[0];
}
```

```expect
pass
```
