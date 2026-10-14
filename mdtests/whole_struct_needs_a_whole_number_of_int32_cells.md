# A whole struct is a whole number of `int32` cells

`*p` holds a struct as `int32` cells, so a struct whose size is not a
multiple of four bytes has no whole-object form yet. The clause is refused
by name; its fields can still be owned one by one.

```c filename=whole_struct_needs_a_whole_number_of_int32_cells.c
struct pair_of_bytes { char a; char b; };

void set(struct pair_of_bytes *q) {
    q->a = 1;
}
```

```click
verifying "whole_struct_needs_a_whole_number_of_int32_cells.c";

void set(struct pair_of_bytes* q) {
    owns *q;
    ensures q->a == 1;
}
```

```expect
fail: a whole object cannot represent the 2-byte `struct pair_of_bytes` as an int32-aligned memory segment
```
