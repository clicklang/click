# external function contracts carry memory effects

```c filename=caller.c
int32 caller(int32 p[]) {
    int32 ignored;
    ignored = external_set(p);
    return p[0];
}
```

```click
import "external_set.interface.click";
verifying "caller.c";

int32 caller(int32 p[]) {
    owns p[0..1];
    ensures result == 0;
}
```

```expect
pass
```
