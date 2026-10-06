# Checked Integer equality rewriting

An explicitly cited Integer equality rewrites occurrences inside mathematical
products, sums, differences, negations and truncating quotient/remainder terms.
The equality must already be available, in either direction. Rewriting refines
the goal; it does not establish the refined proposition.

```click
theorem integer_product_congruence(a: Integer, b: Integer, d: Integer) {
    requires a == b;
    ensures a * d + a == b * d + b by {
        rewrite(a == b);
        simp();
    }
}

theorem integer_compound_rewrite(a: Integer, b: Integer, d: Integer) {
    requires a == b;
    requires d != 0;
    ensures a * d + a == b * d + b by {
        rewrite(a == b);
        simp();
    }
    ensures truncating_quotient(a, d) == truncating_quotient(b, d) by {
        rewrite(a == b);
        simp();
    }
    ensures truncating_remainder(a, d) == truncating_remainder(b, d) by {
        rewrite(a == b);
        simp();
    }
    ensures -(a - d) == -(b - d) by {
        rewrite(b == a);
        simp();
    }
}
```

```expect
pass
```
