# Ordinary generic parameters do not admit integer ordering

The trusted subrange law's supported index formats do not grant ordering to
an arbitrary type parameter in a user theorem.

```click
theorem ordered<T>(a: T, b: T) {
    requires a <= b;
    ensures true by { normalize(); }
}
```

```expect
fail: ordering is not defined for a generic or algebraic value
```
