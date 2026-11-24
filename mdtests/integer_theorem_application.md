# Integer theorem application

```click
theorem add_one(x: Integer) {
    requires x == x;
    ensures x + 1 > x by close();
}

theorem use_add_one(x: Integer) {
    requires x == x;
    ensures x + 1 > x by {
        apply(add_one(x));
    }
}
```

```expect
pass
```
