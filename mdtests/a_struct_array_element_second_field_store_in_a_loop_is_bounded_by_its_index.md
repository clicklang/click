# A struct array element's later field store in a loop is bounded by its index

`items[i].y = 7;` writes four bytes past the start of element `i`. The field
offset stays inside the eight-byte element, so the index bound alone proves
the store in range, as for the first field.

```c filename=struct_array_element_second_field_store.c
struct point { int32 x; int32 y; };
int32 fill_second_fields() {
    struct point items[4];
    int32 i;
    i = 0;
    while (i < 2) {
        items[i].y = 7;
        i = i + 1;
    }
    return 0;
}
```

```click
verifying "struct_array_element_second_field_store.c";

int32 fill_second_fields() {
    ensures result == 0;
} by {
    step(); step(); step();
    loop { decreases 2 - i; invariant i >= 0; invariant i <= 2; }
    execute(); simp();
}
```

```expect
pass
```
