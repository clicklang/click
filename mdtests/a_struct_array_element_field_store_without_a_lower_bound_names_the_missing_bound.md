# A struct array element's field store without a lower bound names the missing bound

The invariant bounds `i` above but not below, so `items[i].x` may index
before the array. The refusal states the index bound the C frontend checks
for the element and the facts about `i` it had, which show the missing
`i >= 0`.

```c filename=struct_array_element_field_store_without_lower_bound.c
struct point { int32 x; int32 y; };
int32 fill_first_fields_unbounded_below() {
    struct point items[4];
    int32 i;
    i = 0;
    while (i < 2) {
        items[i].x = 7;
        i = i + 1;
    }
    return 0;
}
```

```click
verifying "struct_array_element_field_store_without_lower_bound.c";

int32 fill_first_fields_unbounded_below() {
    ensures result == 0;
} by {
    step(); step(); step();
    loop { decreases 2 - i; invariant i <= 2; }
    execute(); simp();
}
```

```expect
fail: could not show `i >= 0 && i < 4` from the facts `i < 2`, `i <= 2`
```
