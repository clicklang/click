# Variable arguments are sequenced as arguments

Each variable argument is an argument of the call, so a call in one and a
read of the object it may change in another are unsequenced, and refused as
they are for named arguments.

```c filename=variable_arguments_are_sequenced_as_arguments.c
int note(int count, ...);
int bump(int *p);

int run(int a) {
    return note(1, bump(&a), a);
}
```

```click
verifying "variable_arguments_are_sequenced_as_arguments.c";

extern int32 bump(int32* p) {
    owns p[0..1];
    ensures result == 0;
}

extern int32 note(int32 count, ...args) {
    ensures result == 0;
}

int32 run(int32 a) {
    ensures result == 0;
}
```

```expect
fail:variable_arguments_are_sequenced_as_arguments.c:5: an expression call and a potentially aliased read in separate function arguments are not supported
```
