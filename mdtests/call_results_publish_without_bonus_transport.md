# Call results and postconditions publish without bonus transport

The statement-publication discovery guard remains active while a call assigns
its symbolic return value. Both the assignment equality and the callee's
postcondition are available without automatic statement-exit fact transport.

```c filename=call.c
int32 caller(int32* p) {
    int32 x;
    x = inspect(p);
    return x;
}
```

```click
verifying "call.c";
extern int32 inspect(int32* p) {
    views *p;
    ensures result == *p;
}
int32 caller(int32* p) {
    owns *p;
    ensures result == *p;
} by {
    step();
    step();
    have x == *p by { assumption(); }
    step();
}
```

```expect
pass
```
