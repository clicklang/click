# Resource arguments distinguish the return value from the C parameter

```c filename=bump.c
int32 bump(int32 result) {
    return result + 1;
}
```

```click
abstract resource pair(returned: int32, input: int32);

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
pass
```
