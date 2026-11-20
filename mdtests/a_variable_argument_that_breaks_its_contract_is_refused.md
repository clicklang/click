# A variable argument that breaks its contract is refused

The contract requires the first variable argument to be a signed `int`. The
call passes an `unsigned int` first, a `UInt`, so it is refused.

```c filename=a_variable_argument_that_breaks_its_contract_is_refused.c
int log_values(int count, ...);

int run(int a, unsigned int b) {
    return log_values(2, b, a);
}
```

```click
verifying "a_variable_argument_that_breaks_its_contract_is_refused.c";

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

extern int32 log_values(int32 count, ...args) {
    requires first_is_int(args);
    ensures result == count;
}

int32 run(int32 a, uint32 b) {
    ensures result == 2;
}
```

```expect
fail:unproved obligation: `first_is_int(List<VarArg>::Cons(VarArg::UInt(b), List<VarArg>::Cons(VarArg::Int(a), List<VarArg>::Nil()))) == true`
```
