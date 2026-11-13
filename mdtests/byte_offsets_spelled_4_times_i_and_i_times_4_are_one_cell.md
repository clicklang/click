# byte offsets spelled 4 * i and i * 4 are one cell

The store writes `u[4 * i]` and the read takes `u[i * 4]`. Both are byte
offsets, kept as written, and they are different terms: the graph has no
commutativity. Each is element `i` at stride four where its product does not
wrap, which the bounds on `i` decide, so memory resolution compares them in
element coordinates and the read is the store.

```c filename=byte_offsets_spelled_4_times_i_and_i_times_4_are_one_cell.c
int get(unsigned char* u, int i) {
    u[4 * i] = 7;
    return u[i * 4];
}
```

```click
verifying "byte_offsets_spelled_4_times_i_and_i_times_4_are_one_cell.c";

int get(unsigned char* u, int i) {
    requires i >= 0;
    requires i < 4;
    owns u[0..16];
    ensures result == 7;
}
```

```expect
pass
```
