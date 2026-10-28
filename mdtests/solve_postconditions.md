# the omitted proof proves local postcondition normalization

This checks the omitted proof's conservative closer. It proves straight-line
postconditions by deterministic local normalization, not by loop verification or
effect reasoning.

```c filename=solve_postconditions.c
int32 solve_postconditions(int32 x) {
    return x;
}
```

```click
verifying "solve_postconditions.c";

int32 solve_postconditions(int32 x) {
    ensures add_zero: result == x + 0;
    ensures prop_solve: result == x and not (result != x);
}
```

```expect
pass
```
