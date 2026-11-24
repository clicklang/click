# The call's output precedes its destination write

The call changes `x` to seven, then assigning its result changes `x` to three.
The two effects have independently nameable endpoints in the original C
statement; its retained call result needs no synthetic C local.

```c filename=call_destination.c
extern int replace(int *p);
int caller(void) {
    int x = 0;
    x = replace(&x);
    return x;
}
```

```click
verifying "call_destination.c";
extern int32 replace(int32 *p) {
    owns *p;
    ensures *p == 7;
    ensures result == 3;
}
int32 caller() {
    ensures result == 3;
} by {
    step_until(statement(1).call(0).entry);
    step();
    have at(statement(1).call(0).exit, x == 7) by { close(); }
    step();
    have at(statement(1).assignment(x, 0).exit, x == 3) by { close(); }
    step();
    close();
}
```

```expect
pass
```
