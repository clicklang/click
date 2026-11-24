# Boolean equality guards in machine conditionals

```click
theorem equal_guard(a: Bool, b: Bool, x: int32) {
    ensures (a == b) implies (if a == b { x } else { 3 }) == x by {
        intro() {
            normalize() using { a == b; };
        }
    }
}

theorem unequal_guard(a: Bool, b: Bool, x: uint64) {
    ensures (a != b) implies (if a == b { x } else { 3u64 }) == 3u64 by {
        intro() {
            normalize() using { a != b; };
        }
    }
}
```

```expect
pass
```
