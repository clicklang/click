# A struct array element's later field store past the last element is refused

The loop's last iteration writes `items[4].y`, a field of an element past
the end of `items`. The field offset lies inside an element, but the element
does not lie inside the array, so the store is refused.

```c filename=struct_array_element_second_field_store_past_end.c
struct point { int32 x; int32 y; };
int32 fill_too_many_second_fields() {
    struct point items[4];
    int32 i;
    i = 0;
    while (i < 5) {
        items[i].y = 7;
        i = i + 1;
    }
    return 0;
}
```

```click
verifying "struct_array_element_second_field_store_past_end.c";

int32 fill_too_many_second_fields() {
    ensures result == 0;
} by {
    step(); step(); step();
    loop { decreases 5 - i; invariant i >= 0; invariant i <= 4; }
    execute(); simp();
}
```

```expect
fail: could not show `i >= 0 && i < 4`
```
