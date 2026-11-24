# A false Integer goal is refused by `close() using`

```click
theorem integer_solve_using_false(x: Integer) {
    ensures x > x + 1 by {
        close() using {  };
    }
}

theorem integer_constant_solve_using_false(x: Integer) {
    ensures 1 == 0 by {
        close() using {  };
    }
}
```

```expect
fail: `close() using`
```
