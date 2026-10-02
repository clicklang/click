# An unnamed prototype is still checked against later declarations

Omitting the names does not relax the parameter types.

```c filename=c_unnamed_prototype_parameter_type_conflict.c
extern int pick(int, const int *);
extern int pick(int value, int *other);

int32 run(int32 value) {
    return value;
}
```

```click
verifying "c_unnamed_prototype_parameter_type_conflict.c";

int32 run(int32 value) {
    ensures result == value by auto;
}
```

```expect
fail: conflicting declarations for function `pick`
```
