# A heap struct array element's field store in a loop is covered by its ownership

`p[i].y = 7;` writes the second field of element `i` through a struct
pointer. A struct pointer's owned range counts structs, so
`owns p[0..4]` holds four eight-byte elements, and the index bound places
every written field inside it.

```c filename=heap_struct_array_element_field_store.c
struct point { int32 x; int32 y; };
int32 fill_heap_second_fields(struct point* p) {
    int32 i;
    i = 0;
    while (i < 4) {
        p[i].y = 7;
        i = i + 1;
    }
    return 0;
}
```

```click
verifying "heap_struct_array_element_field_store.c";

int32 fill_heap_second_fields(struct point* p) {
    owns p[0..4];
    ensures result == 0;
} by {
    step(); step();
    loop { decreases 4 - i; invariant i >= 0; invariant i <= 4; }
    execute(); simp();
}
```

```expect
pass
```
