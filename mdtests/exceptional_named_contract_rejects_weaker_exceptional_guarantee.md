# A throwing callback must meet its contract's exceptional guarantee

`helper` may throw `8`, which `Fallible` does not allow, so it cannot be
passed where `Fallible` is required.

```c filename=exceptional_named_contract_rejects_weaker_exceptional_guarantee.c
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
verifying "exceptional_named_contract_rejects_weaker_exceptional_guarantee.c";

contract int32 Fallible(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}

int32 apply(int32 (*f)(int32), int32 x) throws int32 {
    requires Fallible(f);
    ensures result == x;
    exceptional ensures exception == 7;
}

int32 helper(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 8;
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
fail: function `helper` does not satisfy named contract `Fallible`
```
