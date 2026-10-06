# simp refuses a bound its premises do not give before function exit

The negative of `mdtests/simp_reads_bounds_before_function_exit.md`: `x`'s
bounds put `x + 1` in `[1, 101]`, which does not give `x + 1 >= 2`.

```c filename=simp_refuses_a_bound_before_function_exit.c
int32 inc(int32 x) {
    return x + 1;
}
```

```click
verifying "simp_refuses_a_bound_before_function_exit.c";

int32 inc(int32 x) {
    requires x >= 0 and x <= 100;
    ensures result >= 0 by {
        have x + 1 >= 2 by { simp(); }
        execute();
        simp();
    }
}
```

```expect
fail: could not establish `(x + 1) >= 2`
```
