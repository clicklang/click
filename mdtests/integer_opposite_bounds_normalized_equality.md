# Equality from normalized opposite bounds

Negated successor bounds normalize to opposite bounds, even though their
source operands differ. The generated equality must verify after expansion.

```click
theorem pinned(x: Integer, b: Integer) {
    requires b <= x;
    requires not (b + 1 <= x);
    ensures x == b by { arithmetic() using { b <= x; not (b + 1 <= x); } }
}
```

```expect
pass
```
