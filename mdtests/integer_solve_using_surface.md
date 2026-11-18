# Integer goals close by `solve() using`

```click
theorem integer_solve_using_success(x: Integer) {
    ensures x + 1 > x by {
        solve() using {  };
    }
}

theorem integer_constant_solve_using(x: Integer) {
    ensures 0 == 0 by {
        solve() using {  };
    }
}
```

```expect
pass
```
