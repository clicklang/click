# Normalization uses ambient equalities between C pointer parameters

C pointer parameters use offsets in a shared block. Their explicitly assumed
whole-offset equalities participate in the trusted graph's transitive closure.

```c filename=pointer_equal.c
void keep(int32* a, int32* b, int32* c) { }
```

```click
verifying "pointer_equal.c";

void keep(int32* a, int32* b, int32* c) {
    requires a == b;
    requires b == c;
    ensures a == c;
} by {
    execute();
    normalize() using { }
}
```

```expect
pass
```
