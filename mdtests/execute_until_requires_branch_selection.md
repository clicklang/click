# execute until requires a determined branch

```c filename=execute_until_unresolved_branch.c
int32 execute_until_unresolved_branch(int32 flag) {
    if (flag) {
        flag = 1;
    } else {
        flag = 0;
    }
    return flag;
}
```

```click
verifying "execute_until_unresolved_branch.c";

int32 execute_until_unresolved_branch(int32 flag) {
    ensures result >= 0 by {
        step_until(region(3));
    }
}
```

```expect
fail: could not prove that the next C `if` condition `"execute_until_unresolved_branch.c"::execute_until_unresolved_branch.parameter(0)` is one exact truth value
```
