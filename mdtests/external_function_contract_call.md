# external function contracts apply as explicit assumptions

An external declaration has no C body, but its contract is still applied at
the call site. The caller must establish the external precondition and may use
the external postcondition.

```c filename=caller.c
int32 caller(int32 x) {
    int32 result;
    result = external_identity(x);
    return result;
}
```

```click
import "external_identity.interface.click";
verifying "caller.c";

int32 caller(int32 x) {
    requires x >= 0;
    ensures result == x;
}
```

```expect
pass
```
