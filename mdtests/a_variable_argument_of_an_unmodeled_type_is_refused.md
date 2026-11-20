# A variable argument of an unmodeled type is refused

Click models variable arguments of type `int`, `unsigned int`, `long` and
`unsigned long`, and narrower integers, which C promotes to `int`. A pointer
argument has no `VarArg` case, so the call is refused at its line.

```c filename=a_variable_argument_of_an_unmodeled_type_is_refused.c
int report(int code, ...);

int run(int *p) {
    return report(1, p);
}
```

```click
verifying "a_variable_argument_of_an_unmodeled_type_is_refused.c";

extern int32 report(int32 code, ...args) {
    ensures result == code;
}

int32 run(int32* p) {
    ensures result == 1;
}
```

```expect
fail:a_variable_argument_of_an_unmodeled_type_is_refused.c:4: argument 2 of `report` has type `Int32Pointer`; Click models variable arguments of type `int`, `unsigned int`, `long` and `unsigned long`
```
