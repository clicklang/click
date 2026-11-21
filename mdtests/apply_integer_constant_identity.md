# Explicit theorem application accepts a computed Integer equality

The written premise evaluates to true. The instantiated requirement must
accept the same fact when its constant expression remains structural.

```click
theorem equality_gives_order(a: Integer, b: Integer) {
    requires a == b;
    ensures a <= b by { rewrite(a, b); known(); }
}

theorem concrete_application() {
    ensures 0 <= 0 by {
        have 0 == 0 + 0 by { known(); }
        apply(equality_gives_order(0, 0 + 0)) using { 0 == 0 + 0; };
        known();
    }
}
```

```expect
pass
```
