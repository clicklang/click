# A retained view still excludes a callee write

The call's folded owner projects the same cell the caller views. The
diagnostic identifies the write as a proven conflict with the view.

```c filename=overlap.c
void mutate(int32 *p) { *p = 1; }
int32 observe(int32 *p) { int32 value = *p; mutate(p); return value; }
```
```click
verifying "overlap.c";
resource item(p: int32*) { owns *p; }
void mutate(int32* p) { owns item(p); } by {
    unfold(item(p));
    step_until(function.exit);
    fold(item(p));
    solve();
}
int32 observe(int32* p) {
    views *p;
    owns item(p);
    ensures result == *p;
}
```

```expect
fail: the write by `mutate` overlaps a live view
```
