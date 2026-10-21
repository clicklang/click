# A retained view still excludes a callee write

```c filename=overlap.c
void mutate(int32 *p) { *p = 1; }
int32 observe(int32 *p) { int32 value = *p; mutate(p); return value; }
```
```click
verifying "overlap.c";
resource item(p: int32*) { owns *p; }
void mutate(int32* p) { owns item(p); } by {
    unfold(item(p));
    execute();
    fold(item(p));
    simp();
}
int32 observe(int32* p) {
    views *p;
    owns item(p);
    ensures result == *p;
} by { execute(); simp(); }
```

```expect
fail: stable-view memory access conflicts with an active loan
```
