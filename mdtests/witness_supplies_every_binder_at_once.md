# One `witness` supplies every binder of an existential

`witness(value, ...)` gives each binder of the existential goal its
value, in the order written, as one step. `obtain` is its dual: it opens an
available existential and binds every name at once.

```click
theorem split_sum(n: Integer) {
    requires 0 <= n;
    ensures exists (a: Integer, b: Integer) { a + b == n and 0 <= a and 0 <= b } by {
        witness(n, 0);
        close();
    }
}

theorem reopen(n: Integer) {
    requires exists (a: Integer, b: Integer) { a + b == n and 0 <= a and 0 <= b };
    ensures exists (b: Integer, a: Integer) { a + b == n and 0 <= a and 0 <= b } by {
        let (a, b) = obtain(exists (a: Integer, b: Integer) { a + b == n and 0 <= a and 0 <= b });
        witness(b, a);
        close();
    }
}
```

```expect
pass
```
