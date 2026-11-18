# A freeing call proves separation for the whole allocation

```c filename=verified_call_allocation_retirement_separation.c
void release(unsigned char *p);
void release_beside_view(unsigned char *p, const unsigned char *q) {
    release(p);
}
```

```click
verifying "verified_call_allocation_retirement_separation.c";

extern void release(uint8 *p) {
    consumes allocation(p, 4);
}

void release_beside_view(uint8 *p, const uint8 *q) {
    consumes allocation(p, 4);
    views q[0..1];
    requires separate(memory(((p as (void *)) as (uint8 *))[0..4]), memory(q[0..1]));
} by {
    step() by { known(); }
}
```

```expect
pass
```
