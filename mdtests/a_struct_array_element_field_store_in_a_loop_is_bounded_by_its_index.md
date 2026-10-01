# A struct array element's field store in a loop is bounded by its index

`items[i].x = 7;` addresses the first field of element `i` of a struct
array. The loop invariant bounds `i` exactly as it would for a scalar store
`values[i] = 7;`, so the same element check proves the store in range: the
index is an element of the array and the field lies inside its element.

```c filename=struct_array_element_field_store.c
struct point { int32 x; int32 y; };
int32 fill_first_fields() {
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
verifying "struct_array_element_field_store.c";

int32 fill_first_fields() {
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
