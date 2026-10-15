# A call through a throwing callback must be declared to throw

`apply` calls through a callback whose contract may throw, so a signature
without `throws` is refused.

```c filename=exceptional_named_contract_rejects_undeclared_throw.c
int32 apply(int32 (*f)(int32), int32 x) {
    return f(x);
}

int32 helper(int32 x) {
    return x;
}

int32 steady(int32 x) {
    return x;
}

int32 caller(int32 x) {
    return apply(helper, x);
}

int32 calm(int32 x) {
    return apply(steady, x);
}
```

```click
verifying "exceptional_named_contract_rejects_undeclared_throw.c";

contract int32 Fallible(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}

int32 apply(int32 (*f)(int32), int32 x) {
    requires Fallible(f);
    ensures result == x;
}

int32 helper(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}

int32 steady(int32 x) {
    ensures result == x;
}

int32 caller(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}

int32 calm(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}
```

```expect
fail: apply produced an exceptional outcome not declared by its signature
```
