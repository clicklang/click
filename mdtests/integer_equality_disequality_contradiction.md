# Integer equality and disequality are opposite conditions

The exact opposite remains available in either orientation, including after
an equality has been introduced by an ordinary theorem application.

```click
theorem opposite(a: Integer, b: Integer) {
    requires a == b;
    requires a != b;
    ensures false by { contradiction(a == b); }
}

theorem mirrored(a: Integer, b: Integer) {
    requires a == b;
    requires b != a;
    ensures false by { contradiction(a == b); }
}
```

```expect
pass
```
