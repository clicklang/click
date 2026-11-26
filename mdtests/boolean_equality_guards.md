# Boolean equality guards in machine conditionals

```click
theorem equal_guard(a: Bool, b: Bool, x: int32) {
    ensures (a == b) implies (if a == b { x } else { 3 }) == x by {
        intro() {
            rewrite(a, b);
            close();
        }
    }
}

theorem uint64_conditional_false_branch(guard: Bool, when_true: uint64, when_false: uint64) {
    requires not guard;
    ensures (if guard { when_true } else { when_false }) == when_false by close();
}

theorem unequal_guard(a: Bool, b: Bool, x: uint64) {
    ensures (a != b) implies (if a == b { x } else { 3u64 }) == 3u64 by {
        intro() {
            apply(uint64_conditional_false_branch((if a == b { true } else { false }), x, 3u64));
        }
    }
}
```

```expect
pass
```
