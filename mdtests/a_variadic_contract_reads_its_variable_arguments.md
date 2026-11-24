# A variadic contract reads its variable arguments as a list

A call to a variadic function passes its variable arguments to the
`extern` contract as its last parameter, `...args`: one `List<VarArg>`,
first argument first, each after the default argument promotions. Here the
contract requires the first variable argument to be an `int` and returns
it, and the call passes `a` before `b`, so the precondition holds and `run`
returns `a`. The step's precondition is stated over the list the call
passes, and `close()` proves it by evaluating `first_is_int` on it.

```c filename=a_variadic_contract_reads_its_variable_arguments.c
int first(int count, ...);

int run(int a, unsigned int b) {
    return first(2, a, b);
}
```

```click
verifying "a_variadic_contract_reads_its_variable_arguments.c";

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

function first_is_int(args: List<VarArg>) -> Bool {
    match args {
        List::Nil => false,
        List::Cons(head, tail) => match head {
            VarArg::Int(value) => true,
            VarArg::UInt(value) => false,
            VarArg::Long(value) => false,
            VarArg::ULong(value) => false,
        },
    }
}

extern int32 first(int32 count, ...args) {
    requires first_is_int(args);
    ensures result == first_int(args);
}

int32 run(int32 a, uint32 b) {
    ensures result == a;
} by {
    have first_is_int(List::Cons(VarArg::Int(a), List::Cons(VarArg::UInt(b), List::Nil))) by {
        close();
    }
    step() by { close(); }
    step();
}
```

```expect
pass
```
