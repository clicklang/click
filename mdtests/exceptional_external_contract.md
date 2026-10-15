# An external function may throw

An `extern` declaration may carry `throws int32` and `exceptional ensures`.
A direct call and a call through a pointer under a throwing named contract
both take its two outcomes.

```c filename=exceptional_external_contract.c
int32 parse(int32 x);

int32 apply(int32 (*f)(int32), int32 x) {
    return f(x);
}

int32 direct(int32 x) {
    return parse(x);
}

int32 indirect(int32 x) {
    return apply(parse, x);
}
```

```click
verifying "exceptional_external_contract.c";

extern int32 parse(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}

contract int32 Fallible(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}

int32 apply(int32 (*f)(int32), int32 x) throws int32 {
    requires Fallible(f);
    ensures result == x;
    exceptional ensures exception == 7;
}

int32 direct(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}

int32 indirect(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}
```

```expect
pass
```
