# Smart arithmetic names an `int32` atom, not its `uint32` cast

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `solve() using { ... }`.

```c filename=arithmetic_names_an_int32_atom_beside_its_uint32_cast.c
int32 bounded(int32 m, int32 n) {
    return m;
}

int32 bounded_by_expansion(int32 m, int32 n) {
    return m;
}
```

```click
verifying "arithmetic_names_an_int32_atom_beside_its_uint32_cast.c";

int32 bounded(int32 m, int32 n) {
    requires m < n;
    requires (n as uint32) <= 1073741823u32;
    ensures result < 2147483647;
} by {
    have m < 2147483647 by {
        solve() using { m < n; (n as uint32) <= 1073741823u32; };
    }
}

int32 bounded_by_expansion(int32 m, int32 n) {
    requires m < n;
    requires (n as uint32) <= 1073741823u32;
    ensures result < 2147483647;
} by {
    have m < 2147483647 by {
        solve() using { m < n; };
    }
    step();
    have result < 2147483647 by {
        known();
    }
    known();
}
```

```expect
pass
```
