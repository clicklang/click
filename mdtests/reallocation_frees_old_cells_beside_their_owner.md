# reallocation frees the old cells beside their owner

`replace_cells` swaps a composite's backing array for a fresh one-cell
allocation and frees the old array. The composite's allocation size is the
dependent product `owner->cap * 4`, so opening it compares that product
across the composite's two spellings. On the success path the postcondition
`result == 0 implies owner->cap == old(owner->cap)` relates the owner's field
across the `free`, which the memory DAG may cross only because the freed
allocation is separate from the owner's cells. This catches a free edge that
is not bridged by the allocation's resource separation, and a dependent
allocation size that does not match its own spelling.

```c filename=reallocation_frees_old_cells_beside_their_owner.c
struct cell_owner {
    int32 cap;
    int32* data;
};

int32 replace_cells(struct cell_owner* owner) {
    int32* old_data;
    int32* new_data;

    old_data = owner->data;
    new_data = malloc(4);
    if (new_data == 0) {
        return 0;
    }
    owner->data = new_data;
    owner->cap = 1;
    free(old_data);
    return 1;
}
```

```click
resource allocated_cells(owner: struct cell_owner*) {
    owns owner->cap;
    owns owner->data;
    owns allocation(owner->data, owner->cap * 4);
    owns owner->data[0..owner->cap];
}

verifying "reallocation_frees_old_cells_beside_their_owner.c";

int32 replace_cells(struct cell_owner* owner) {
    consumes allocated_cells(owner);
    produces allocated_cells(owner);
    ensures result == 0 implies owner->cap == old(owner->cap);
} by {
    open(allocated_cells(owner)) {
    }
    unfold(allocated_cells(owner));
    execute();
    fold(allocated_cells(owner));
    simp();
}
```

```expect
pass
```
