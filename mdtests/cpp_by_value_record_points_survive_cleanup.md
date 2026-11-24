# A copied C++ record keeps its entry observation after the call

The callee changes its private parameter. Its proof checks the changed field
at the return statement's entry. After the call, the caller uses the saved
parameter to read the copy's entry value and checks that its own field
still has the original value.

```cpp filename=copy_points.cpp function=probe profile=normal_only
struct View { unsigned int count; };

unsigned int shorten(View value) noexcept {
    value.count = 7;
    return value.count;
}

unsigned int probe(const View& source) noexcept {
    shorten(source);
    return source.count;
}
```

```click
verifying "copy_points.cpp";

uint32 shorten(struct View value) {
    requires value.count == 13u32;
    ensures result == 7u32;
} by {
    step_until(function.exit);
    have at(region(1).entry, value.count) == 7u32 by { known(); }
}

uint32 probe(const struct View& source) {
    views source.count;
    requires source.count == 13u32;
    ensures result == 13u32;
    ensures source.count == old(source.count);
} by {
    step_until(call(0).entry);
    step() {
        requires call(0).parameter(value).count == 13u32 by solve();
    }
    step_until(function.exit);
    have at(call(0).entry, call(0).parameter(value).count) == 13u32 by { known(); }
    have call(0).result == 7u32 by { known(); }
    have result == old(source.count) by { known(); }
}
```

```expect
pass
```
