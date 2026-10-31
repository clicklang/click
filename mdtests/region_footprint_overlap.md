# A statement footprint includes the cell it writes

```c filename=write.c
void write_cell(int *p) { *p = 7; }
```

```click
verifying "write.c";
void write_cell(int *p) { owns *p; } by {
    step();
    have separate(statement(0).footprint, memory(*p)) by {
        normalize() using {};
    }
}
```

```expect
fail: goal did not normalize to true
```
