# `decreases` naming a non-parameter name is refused

A numeric `decreases` clause is read once at function entry. `m` here is a
body local that does not exist at that point, so no entry measure can be
captured. This is an opening error, rather than a later body-analysis error.

```c filename=c_decreases_rejects_non_parameter_binder.c
int32 countdown(int32 n) {
    int32 m;

    if (n <= 0) {
        return 0;
    }
    m = n - 1;
    return countdown(m);
}
```

```click
verifying "c_decreases_rejects_non_parameter_binder.c";

int32 countdown(int32 n) {
    requires n >= 0;
    decreases m;
    ensures result == 0;
}
```

```expect
fail: the `decreases` measure `m` of `countdown` could not be read at its own entry state
```
