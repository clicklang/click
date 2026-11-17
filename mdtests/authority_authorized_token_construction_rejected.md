# Constructing an authorized token is refused

`pair` is an `authorized abstract resource`, so building one from nothing
would create a population member without its authority. Construction is
refused.

```c filename=bump.c
int32 bump(int32 result) {
    return result + 1;
}
```

```click
authorized abstract resource pair(returned: int32, input: int32);

verifying "bump.c";

int32 bump(int32 result) {
    requires 0 <= program::result and program::result <= 100;
    constructs pair(result, program::result);
    produces pair(result, program::result) by {
        step_until(function.exit);
        construct(pair(result, program::result));
    }
}
```

```expect
fail: resource construction may create untracked members
```
