# external function calls require their declared preconditions

```c filename=caller.c
int32 caller() {
    int32 result;
    result = external_identity(-1);
    return result;
}
```

```click
import "external_identity.interface.click";
verifying "caller.c";

int32 caller() {
    ensures result == -1;
}
```

```expect
fail: unproved obligation: `-1 >= 0`
```
