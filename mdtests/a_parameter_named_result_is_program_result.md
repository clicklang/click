# A parameter named `result` is `program::result`

Bare `result` is the returned pointer, here `next`; the parameter named
`result` is `program::result`, in the contract, in a postcondition's proof,
and under `old(...)`, including through a field read.

```c filename=select.c
struct object { int32 value; };
struct object* select(struct object* result, struct object* next) {
    return next;
}
```

```click
verifying "select.c";
struct object* select(struct object* result, struct object* next) {
    views result->value;
    views next->value;
    requires program::result->value == 3 and next->value == 7;
    ensures program::result->value == 3 by {
        step_until(function.exit);
        have program::result->value == 3 by { known(); }
        have old(program::result->value) == 3 by { known(); }
    }
    ensures result->value == 7;
}
```

```expect
pass
```
