# An array inside a struct array element in a loop is bounded by both indices

`items[i].cells[i]` indexes element `i` of the struct array and then cell
`i` of the array inside it. The outer index is bounded by the struct array's
element count and the inner one by the field array's, so the store is in
range for `0 <= i < 3`.

```c filename=array_inside_struct_array_element.c
struct row { int32 tag; int32 cells[3]; };
int32 fill_diagonal() {
    struct row items[4];
    int32 i;
    i = 0;
    while (i < 3) {
        items[i].cells[i] = 7;
        i = i + 1;
    }
    return 0;
}
```

```click
verifying "array_inside_struct_array_element.c";

int32 fill_diagonal() {
    ensures result == 0;
} by {
    step(); step(); step();
    loop { decreases 3 - i; invariant i >= 0; invariant i <= 3; }
    execute(); simp();
}
```

```expect
pass
```
