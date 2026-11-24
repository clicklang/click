# Compose signed comparisons with transitivity theorems

The two theorem applications carry a strict comparison through weak bounds.
A strict comparison between literals can also provide the strict link.

```click
theorem explicit_chain(a: int32, b: int32, c: int32, d: int32) {
    requires a <= b;
    requires b < c;
    requires c <= d;
    ensures a < d by {
        have a < c by {
            apply(click::integer::int32_less_equal_less_than_transitive(a, b, c));
        }
        apply(click::integer::int32_less_than_less_equal_transitive(a, c, d));
    }
}
theorem explicit_chain_through_literals(a: int32, b: int32) {
    requires a <= 1;
    requires 2 <= b;
    ensures a < b by {
        have 1 < 2 by { close(); }
        have a < 2 by {
            apply(click::integer::int32_less_equal_less_than_transitive(a, 1, 2));
        }
        apply(click::integer::int32_less_than_less_equal_transitive(a, 2, b));
    }
}
theorem explicit_weaken(a: int32, b: int32) {
    requires a < b;
    ensures a <= b by {
        apply(click::integer::int32_less_than_implies_less_equal(a, b));
    }
}
```

```expect
pass
```
