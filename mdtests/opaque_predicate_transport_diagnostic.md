# An opaque historical predicate does not prove its current value

The store changes the array version. The entry predicate alone cannot
establish that the current array is sorted.

```c filename=opaque_predicate_transport_diagnostic.c
int32 preserve_sorted(int32 p[3]) {
    p[0] = 1;
    return 0;
}
```

```click
verifying "opaque_predicate_transport_diagnostic.c";

predicate sorted(p: int32[], n: int32) {
    forall (i: int32) {
        forall (j: int32) {
            0 <= i and 0 <= j and i < j and j < n implies p[i] <= p[j]
        }
    }
}

int32 preserve_sorted(int32 p[3]) {
    requires viewable(p[0..3]);
    owns p[0..1];
    requires sorted(p, 3);
    ensures sorted(p, 3);
} by {
    step();
    have sorted(p, 3) by { close() using { at(function.entry, sorted(p, 3)); }; }
}
```

```expect
fail: `close() using` could not prove the current goal from only its listed premises
```
