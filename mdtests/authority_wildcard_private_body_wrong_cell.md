# One member does not authorize writes to another slot

```c filename=wildcard_private_wrong_cell.c
void update(int32* pool, int32* p) { p[1] = 7; }
```

```click resource_semantics=authority
resource slot(pool: int32*, p: int32*) { owns p[0..1]; }
verifying "wildcard_private_wrong_cell.c";
void update(int32* pool, int32* p) {
    owns slot(pool, p);
} by { open(slot(pool, p)) { step(); } execute(); simp(); }
```

```expect
fail: missing resource fact `owns p[1]`
```
