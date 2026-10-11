# `arithmetic_certificate special` is retired

The pointer, finite-float, definedness, and exact Integer rule family of
`arithmetic_certificate` is spelled `rules`. The old spelling `special` is
refused with a diagnostic that names the new one; the same certificate
written with `rules` verifies in
[`integer_bound_exclusion.md`](integer_bound_exclusion.md).

```click
theorem positive_bound_excludes_zero(x: Integer) {
    requires 1 <= x;
    ensures x != 0 by {
        arithmetic_certificate special {
            premise 0: 1 <= x => 1 <= x;
            integer_bound_exclusion bounds [0] => x != 0;
            conclusion 0;
        }
    }
}
```

```expect
fail: `arithmetic_certificate special` is retired: write `arithmetic_certificate rules { ... }`
```
