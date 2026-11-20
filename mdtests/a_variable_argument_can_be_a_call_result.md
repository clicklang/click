# A variable argument can be a call's result

A variable argument is an argument of the call: a call among them is made
first, as for a named argument, and its result is the value the list holds.
The call to `note` is a statement, its result discarded.

```c filename=a_variable_argument_can_be_a_call_result.c
int note(int count, ...);
int twice(int x);

int run(int a) {
    note(1, twice(a));
    return a;
}
```

```click
verifying "a_variable_argument_can_be_a_call_result.c";

function first_int(args: List<VarArg>) -> int32 {
    match args {
        List::Nil => 0,
        List::Cons(head, tail) => match head {
            VarArg::Int(value) => value,
            VarArg::UInt(value) => 0,
            VarArg::Long(value) => 0,
            VarArg::ULong(value) => 0,
        },
    }
}

extern int32 twice(int32 x) {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
}

extern int32 note(int32 count, ...args) {
    ensures result == first_int(args);
}

int32 run(int32 a) {
    requires 0 <= a and a <= 1000;
    ensures result == a;
}
```

```expect
pass
```
