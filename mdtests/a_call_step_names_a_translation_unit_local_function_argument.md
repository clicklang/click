# A call step names a translation-unit-local function argument by its source name

A `static inline` function's execution name carries its translation unit,
`compare#inline:caller.c`, while the sidecar and the C call both write
`compare`. A call step that writes its call compares each written argument
with the call's, so `step(apply(compare, 40, 2), { })` passes the function
the call passes. The shape is the rbtree erase wrapper's
`step(____rb_erase_color(rebalance, root, dummy_rotate), { c: deficit })`
with its `static inline` `dummy_rotate`.

```c filename=apply.c
int32 apply(int32 (*callback)(int32, int32), int32 left, int32 right) {
    int32 result;
    result = callback(left, right);
    return result;
}
```

```c filename=caller.c
int32 apply(int32 (*callback)(int32, int32), int32 left, int32 right);

static inline int32 compare(int32 left, int32 right) {
    return left - right;
}

int32 caller() {
    int32 result;
    result = apply(compare, 40, 2);
    return result;
}
```

```click
verifying "apply.c";
verifying "caller.c";

contract int32 Comparator(int32 left, int32 right) {
    requires 0 <= left;
    requires 0 <= right;
    requires right <= left;
    ensures result == left - right;
}

int32 compare(int32 left, int32 right) {
    requires 0 <= left;
    requires 0 <= right;
    requires right <= left;
    ensures result == left - right by auto();
}

int32 apply(int32 (*callback)(int32, int32), int32 left, int32 right) {
    requires Comparator(callback);
    requires 0 <= left;
    requires 0 <= right;
    requires right <= left;
    ensures result == left - right by auto();
}

int32 caller() {
    ensures result == 38;
} by {
    step();
    let { result: r } = step(apply(compare, 40, 2), { });
    execute();
    auto();
}
```

```expect
pass
```
