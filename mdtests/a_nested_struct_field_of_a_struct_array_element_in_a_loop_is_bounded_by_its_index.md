# A nested struct field of a struct array element in a loop is bounded by its index

`items[i].in.b` is the second field of a struct nested at byte four of each
twelve-byte element. The nested offsets add to a constant inside the element,
so the index bound proves the store in range.

```c filename=nested_struct_field_of_struct_array_element.c
struct inner { int32 a; int32 b; };
struct outer { int32 tag; struct inner in; };
int32 fill_nested_fields() {
    struct outer items[4];
    int32 i;
    i = 0;
    while (i < 4) {
        items[i].in.b = 7;
        i = i + 1;
    }
    return 0;
}
```

```click
verifying "nested_struct_field_of_struct_array_element.c";

int32 fill_nested_fields() {
    ensures result == 0;
} by {
    step(); step(); step();
    loop { decreases 4 - i; invariant i >= 0; invariant i <= 4; }
    execute(); simp();
}
```

```expect
pass
```
