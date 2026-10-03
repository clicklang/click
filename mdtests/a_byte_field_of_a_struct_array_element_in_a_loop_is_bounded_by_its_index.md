# A byte field of a struct array element in a loop is bounded by its index

`struct item` has a one-byte field followed by padding and a four-byte
field. Both stores land inside element `i`, so the index bound proves each
of them in range.

```c filename=byte_field_of_struct_array_element.c
struct item { uint8 tag; int32 value; };
int32 fill_items() {
    struct item items[4];
    int32 i;
    i = 0;
    while (i < 2) {
        items[i].tag = 1;
        items[i].value = 2;
        i = i + 1;
    }
    return 0;
}
```

```click
verifying "byte_field_of_struct_array_element.c";

int32 fill_items() {
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
