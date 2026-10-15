# A callback's named contract may throw

A named contract carries the same `throws int32` channel and `exceptional
ensures` clauses as a function. A call through a pointer under it has both
outcomes, and the caller's contract owes both families. `helper` may throw,
and its exceptional guarantee meets `Fallible`'s; `steady` never throws, which
a contract that may throw allows.

```c filename=exceptional_named_contract.c
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
verifying "exceptional_named_contract.c";

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
pass
```
