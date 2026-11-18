# A false Integer goal is refused by `solve() using`

```click
theorem integer_solve_using_false(x: Integer) {
    ensures x > x + 1 by {
        solve() using {  };
    }
}

theorem integer_constant_solve_using_false(x: Integer) {
    ensures 1 == 0 by {
        solve() using {  };
    }
}
```

```expect
fail: solve
```
