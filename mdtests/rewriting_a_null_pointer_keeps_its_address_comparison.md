# Rewriting a null pointer keeps its address comparison

An address comparison that becomes a comparison with zero after rewriting
uses the same null relation as a directly written comparison. Equality and
inequality work with zero on either side.

```click
theorem nonzero_address_after_null_rewrite(p: void*, q: void*) {
    requires q == 0;
    requires address(p) != 0u64;
    ensures address(q) != address(p) by {
        rewrite(q == 0);
        simp();
    }
}

theorem zero_address_after_null_rewrite(p: void*, q: void*) {
    requires p == 0;
    requires q == 0;
    ensures address(q) == address(p) by {
        rewrite(p == 0);
        normalize() using { q == 0; };
    }
}
```

```expect
pass
```
