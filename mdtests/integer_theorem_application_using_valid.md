# Integer theorem application accepts an explicit exact guard

```click
theorem guarded(x: Integer) {
    requires x == 0;
    ensures x + 1 > x by close();
}

theorem use_guarded(x: Integer) {
    requires x == 0;
    ensures x + 1 > x by {
        apply(guarded(x));
    }
}
```

```expect
pass
```
