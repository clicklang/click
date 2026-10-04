# `outcomes` routes a throw that leaves the function

At a maybe-throwing call outside any `try`, `outcomes` splits the call's
two successors. The `threw` arm steps the call and ends at function exit
with that throw; the `returned` arm steps the call and continues with the
rest of the function, here into a second call's own nested `outcomes`.
Each arm proves the claims its paths owe.

```c filename=outcomes_routes_a_throw_that_leaves_the_function.c
int32 helper(int32 x) { return x; }
int32 caller(int32 x) {
    int32 y = helper(x);
    int32 z = helper(y);
    return z;
}
```

```click
verifying "outcomes_routes_a_throw_that_leaves_the_function.c";

int32 helper(int32 x) throws int32 {
    ensures result == x by auto;
    exceptional ensures exception == 7 by auto;
}

int32 caller(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
} by {
    step();
    outcomes {
        returned => {
            step();
            step();
            outcomes {
                returned => {
                    step();
                    step();
                    simp();
                }
                threw => {
                    step();
                    simp();
                }
            }
        }
        threw => {
            step();
            simp();
        }
    }
}
```

```expect
pass
```
