# An ordinary token is constructed in authority mode

`pair` is an abstract resource declared without `authorized`, so its tokens
are not population members. A function that `constructs` one may build it
from nothing in an authority-mode project, as without authority semantics.

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
    produces pair(result, c(result)) by {
        execute();
        construct(pair(result, c(result)));
    }
}
```

```expect
pass
```
