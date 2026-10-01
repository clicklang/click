# A struct array element's field store past the last element is refused

The loop runs `i` up to `4`, so its last iteration writes `items[4].x`, one
element past the end of `items`. The index bound the invariant supplies does
not place that element inside the array, so the store is refused.

```c filename=struct_array_element_field_store_past_end.c
struct point { int32 x; int32 y; };
int32 fill_too_many_first_fields() {
    struct point items[4];
    int32 i;
    i = 0;
    while (i < 5) {
        items[i].x = 7;
        i = i + 1;
    }
    return 0;
}
```

```click
verifying "struct_array_element_field_store_past_end.c";

int32 fill_too_many_first_fields() {
    ensures result == 0;
} by {
    step(); step(); step();
    loop { decreases 5 - i; invariant i >= 0; invariant i <= 4; }
    execute(); simp();
}
```

```expect
fail: array subobject index must be in [0, 4)
```
