# `unfold(at(point, f(args)))` opens a pure function at that point

A pure function over an array reads the array at the point the call is
spelled at. `replace_first` overwrites `a[0]`, so its result is `head(a)` at
the function's entry, not at its exit. `unfold(at(function.entry, head(a)))`
adds `at(function.entry, head(a)) == at(function.entry, a[0u64])`, the
defining equation at that point. `unfold` used to refuse a call inside
`at(...)` with "unfold requires a defined predicate application".

`solve` uses the same form to evaluate a call a postcondition names at the
call's entry, such as `fprintf`'s `format_length`.

```c filename=unfold_at_a_point_opens_a_pure_function_there.c
int replace_first(int *a) {
    int x = a[0];
    a[0] = 7;
    return x;
}
```

```click
verifying "unfold_at_a_point_opens_a_pure_function_there.c";

function head(a: int32[]) -> int32 {
    a[0u64]
}

int32 replace_first(int32 *a) {
    owns a[0..1];
    requires a[0] > 0;
    ensures result == at(function.entry, head(a));
} by {
    have at(function.entry, head(a)) == at(function.entry, a[0u64]) by {
        unfold(at(function.entry, head(a)));
        close();
    }
}
```

```expect
pass
```
