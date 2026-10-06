# A returned resource cannot replace its C parameter with the return value

```c filename=bump.c
int32 bump(int32 result) {
    return result + 1;
}
```

```click
abstract resource pair(returned: int32, input: int32);

verifying "bump.c";

int32 bump(int32 result) {
    requires 0 <= c(result) and c(result) <= 100;
    constructs pair(result, c(result));
    produces pair(result, result) by {
        execute();
        construct(pair(result, result));
    }
}
```

```expect
fail: resource construction is not authorized
```
