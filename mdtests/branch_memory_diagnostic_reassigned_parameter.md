# A reassigned struct-pointer parameter keeps its current field name

The branch is refused because the proof holds no view of the field. The
message must name the field through the current `cursor`, retaining its
source struct layout without reusing a function-entry pointer value.

```c filename=probe.c
struct cell { int32 left; int32 right; };
int32 probe(struct cell* cursor, struct cell* replacement) {
    cursor = replacement;
    if (cursor->right) return 1;
    return 0;
}
```

```click
verifying "probe.c";
int32 probe(struct cell* cursor, struct cell* replacement) {
    requires replacement != 0;
    ensures result == 0 or result == 1;
} by { execute(); simp(); }
```

```expect
fail: the read requires `views cursor->right`, which is not available
```
