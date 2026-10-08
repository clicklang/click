# Constructing an authorized token is refused

`pair` is an `authorized abstract resource`, so building one from nothing
would create a population member without its authority. Construction is
refused.

```c filename=bump.c
int32 bump(int32 result) {
    return result + 1;
}
```

```click resource_semantics=authority
authorized abstract resource pair(returned: int32, input: int32);

verifying "bump.c";

int32 bump(int32 result) {
    requires 0 <= c(result) and c(result) <= 100;
    constructs pair(result, c(result));
    produces pair(result, c(result)) by {
        execute();
        construct(pair(result, c(result)));
    }
}
```

```expect
fail: resource construction may create untracked members in authority mode
```
