# Variable arguments are promoted

C promotes a variable argument narrower than `int` to `int` (C11
6.5.2.2p6-7): a `char`, `short` or `unsigned char` argument is an `Int`. An
`unsigned int` is a `UInt`, a `long` a `Long` and an `unsigned long` a
`ULong`, and a call with no variable arguments passes `List::Nil`. The
contract's result names the case its first variable argument is.

```c filename=variable_arguments_are_promoted.c
int kind(int count, ...);

int of_char(char c) { return kind(1, c); }
int of_short(short s) { return kind(1, s); }
int of_unsigned_char(unsigned char u) { return kind(1, u); }
int of_unsigned(unsigned int u) { return kind(1, u); }
int of_long(long l) { return kind(1, l); }
int of_unsigned_long(unsigned long l) { return kind(1, l); }
int of_nothing(void) { return kind(0); }
```

```click
verifying "variable_arguments_are_promoted.c";

function first_kind(args: List<VarArg>) -> int32 {
    match args {
        List::Nil => 4,
        List::Cons(head, tail) => match head {
            VarArg::Int(value) => 0,
            VarArg::UInt(value) => 1,
            VarArg::Long(value) => 2,
            VarArg::ULong(value) => 3,
        },
    }
}

extern int32 kind(int32 count, ...args) {
    ensures result == first_kind(args);
}

int32 of_char(char c) { ensures result == 0; }
int32 of_short(int16 s) { ensures result == 0; }
int32 of_unsigned_char(uint8 u) { ensures result == 0; }
int32 of_unsigned(uint32 u) { ensures result == 1; }
int32 of_long(int64 l) { ensures result == 2; }
int32 of_unsigned_long(uint64 l) { ensures result == 3; }
int32 of_nothing() { ensures result == 4; }
```

```expect
pass
```
