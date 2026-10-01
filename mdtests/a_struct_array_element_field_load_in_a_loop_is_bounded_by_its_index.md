# A struct array element's field load in a loop is bounded by its index

Each iteration writes `items[i].y` and reads it back. The read of
`items[i].y` uses the same element bound as the write.

```c filename=struct_array_element_field_load.c
struct point { int32 x; int32 y; };
int32 read_second_fields() {
    struct point items[4];
    int32 i;
    int32 v;
    i = 0;
    v = 0;
    while (i < 4) {
        items[i].y = i;
        v = items[i].y;
        i = i + 1;
    }
    return v;
}
```

```click
verifying "struct_array_element_field_load.c";

int32 read_second_fields() {
    ensures result >= 0;
} by {
    step(); step(); step(); step(); step();
    loop { decreases 4 - i; invariant i >= 0; invariant i <= 4; invariant v >= 0; }
    execute(); simp();
}
```

```expect
pass
```
