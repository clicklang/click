# Theorem discovery accepts equivalent comparison spellings

```click
function fixed(x: Integer) -> Integer { 7 }

theorem lower_bound(x: Integer) {
    requires 0 <= x;
    ensures fixed(x) >= 7 by { unfold(fixed(x)); solve(); }
}

theorem equality(x: Integer) {
    requires 0 <= x;
    ensures fixed(x) == 7 by { unfold(fixed(x)); solve(); }
}

theorem test(value: Integer) {
    requires 0 <= value;
    ensures 7 <= fixed(value) by { close() using { 0 <= value; }; }
    ensures 7 == fixed(value) by { close() using { 0 <= value; }; }
}
```

```expect
pass
```
