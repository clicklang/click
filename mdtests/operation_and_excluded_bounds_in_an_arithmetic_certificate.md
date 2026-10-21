# An arithmetic certificate cites operation and excluded bounds

`click expand` writes the bounds `auto` used as certificate nodes.
`operation_bound => P;` states the bound an unsigned quotient, shift, or
remainder by a constant takes from its operand, and the kernel finds the
operation among `P`'s own terms. `excluded_bound N: D => P;` cites premise `N`,
a disequality with a type endpoint, as the bound it gives. Each is checked
exactly: `P` must be that bound.

```click
theorem shifted_guard(v: uint64) {
    requires (v >> 32) != 0u64;
    ensures 4294967296u64 <= v by {
        arithmetic_certificate {
            negated_goal => to_integer(v) < to_integer(4294967296u64);
            excluded_bound 0: to_integer((v >> 32)) != 0 => 1 <= to_integer((v >> 32));
            scale 1 by 4294967296 => (4294967296 * 1) <= (4294967296 * to_integer((v >> 32)));
            operation_bound => (4294967296 * to_integer((v >> 32))) <= to_integer(v);
            add 0, 2 => (to_integer(v) + (4294967296 * 1)) < (to_integer(4294967296u64) + (4294967296 * to_integer((v >> 32))));
            add 4, 3 => (to_integer(v) + (4294967296 * 1) + (4294967296 * to_integer((v >> 32)))) < (to_integer(4294967296u64) + (4294967296 * to_integer((v >> 32))) + to_integer(v));
            conclusion 5;
        }
    };
}
```

```expect
pass
```
