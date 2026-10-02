# A variadic prototype does not match a fixed-arity one

Variadic and fixed-arity declarations of one function have incompatible
types, so the pair is rejected instead of letting the fixed-arity
declaration make the function callable.

```c filename=c_variadic_conflicting_prototype_rejected.c
int report(int code, ...);
int report(int code);

int32 run(int32 value) {
    return value;
}
```

```click
verifying "c_variadic_conflicting_prototype_rejected.c";

int32 run(int32 value) {
    ensures result == value by auto;
}
```

```expect
fail: conflicting declarations for function `report`
```
