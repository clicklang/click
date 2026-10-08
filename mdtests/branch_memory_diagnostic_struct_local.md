# A struct-pointer local keeps its field name after assignment

The branch is refused because the proof holds no view of the field. The
message must name the field through the current `cursor`, retaining its
source struct layout without reusing a function-entry pointer value.

```c filename=probe.c
struct cell { int32 left; int32 right; };
int32 probe(struct cell* root) {
    struct cell* cursor;
    cursor = root;
    if (cursor->right) return 1;
    return 0;
}
```

```click
verifying "probe.c";
int32 probe(struct cell* root) {
    requires root != 0;
    ensures result == 0 or result == 1;
} by { execute(); simp(); }
```

```expect
fail: the read requires `views cursor->right`, which is not available
```
