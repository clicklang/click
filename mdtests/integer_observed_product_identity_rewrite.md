# Observed Integer products retain source spellings after identity rewrites

Checked rewriting uses the same zero and unit product identities as lowering.
The resulting arithmetic certificates remain checkable independently of search.
Observations retain the complete unsigned range.

```click
theorem zero_product(a: uint32, b: uint32) {
    requires to_integer(b) == 0;
    ensures to_integer(a) * to_integer(b) == 0 by {
        rewrite(to_integer(b) == 0);
        arithmetic() using {};
    }
}

theorem zero_left_product(a: uint32, b: uint32) {
    requires to_integer(b) == 0;
    ensures to_integer(b) * to_integer(a) == 0 by {
        rewrite(to_integer(b) == 0);
        arithmetic() using {};
    }
}

theorem unit_product(a: uint32, b: uint32) {
    requires to_integer(b) == 1;
    ensures to_integer(a) * to_integer(b) == to_integer(a) by {
        rewrite(to_integer(b) == 1);
        arithmetic() using {};
    }
}

theorem unit_left_product(a: uint32, b: uint32) {
    requires to_integer(b) == 1;
    ensures to_integer(b) * to_integer(a) == to_integer(a) by {
        rewrite(to_integer(b) == 1);
        arithmetic() using {};
    }
}

theorem full_unsigned_zero(b: uint32) {
    requires to_integer(b) == 0;
    ensures to_integer(4294967295u32) * to_integer(b) == 0 by {
        rewrite(to_integer(b) == 0);
        arithmetic() using {};
    }
}

theorem full_unsigned_unit(b: uint32) {
    requires to_integer(b) == 1;
    ensures to_integer(4294967295u32) * to_integer(b) == 4294967295 by {
        rewrite(to_integer(b) == 1);
        arithmetic() using {};
    }
}
```

```expect
pass
```
