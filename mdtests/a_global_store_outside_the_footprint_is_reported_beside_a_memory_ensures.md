# a global store outside the footprint is reported beside a memory `ensures`

The function owns `shared.second` and writes `shared.first`, so it is refused
for writing storage outside its owned footprint, as in
`static_struct_field_footprint_rejected.md`. Here the contract also has an
`ensures` that reads memory through `old(...)`. Lowering that claim for the
implicit closer has to resolve the global aggregate `shared` in the entry
state; when it could not, the claim proof failed first with a message naming
no claim, cell, or store, and the footprint refusal never surfaced. The
claim itself holds: `shared.second` is unchanged, so the refusal names the
store to `shared.first`.

```c filename=a_global_store_outside_the_footprint_is_reported_beside_a_memory_ensures.c
struct pair {
    int32 first;
    int32 second;
};

struct pair shared;

int32 f() {
    shared.first = 9;
    return 0;
}
```

```click
verifying "a_global_store_outside_the_footprint_is_reported_beside_a_memory_ensures.c";

int32 f() {
    owns shared.second;
    ensures result == 0;
    ensures shared.second == old(shared.second);
}
```

```expect
fail: write to storage outside the owned footprint: the 4-byte store to `shared.first`
```
