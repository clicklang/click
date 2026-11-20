# A resource scope uses the `with` spelling

The retired tactic points to the new spelling.

```c filename=with_rejects_open_tactic.c
void use_cell(int *p) {}
```

```click
verifying "with_rejects_open_tactic.c";

resource cell(p: int32*) { owns *p; }

void use_cell(int32* p) {
    owns cell(p);
} by {
    open(cell(p)) {}
}
```

```expect
fail: `open` is now `with`
```
