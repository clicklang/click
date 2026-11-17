# A nullable resource's double free is refused in its non-null case

`item_destroy` consumes `owned_item(item)`, which owns the allocation only
when `item` is not null. The proof splits on that guard. In the null case
both `free` calls are no-ops, but in the non-null case the second `free`
ends a lifetime that has already ended, so the contract is refused even
though one of its cases is safe.

```c filename=a_nullable_resource_double_free_is_refused_in_its_non_null_case.c
struct item {
    int value;
};

int item_destroy(struct item *item) {
    free(item);
    free(item);
    return 0;
}
```

```click
verifying "a_nullable_resource_double_free_is_refused_in_its_non_null_case.c";

resource owned_item(item: struct item*) {
    if item != 0 {
        owns allocation(item, sizeof(struct item));
        owns *item;
    }
}

int32 item_destroy(struct item* item) {
    consumes owned_item(item);
    ensures result == 0;
} by {
    if item != 0 { unfold(owned_item(item)); step_until(function.exit); }
    else { unfold(owned_item(item)); step_until(function.exit); }
}
```

```expect
fail: cannot free an allocation whose lifetime has already ended
```
