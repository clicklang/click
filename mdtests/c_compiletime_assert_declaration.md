# A block-scope `error` declaration and its unreachable call

The Linux `compiletime_assert` macro declares, inside a block, an external function with the GNU `error` attribute and calls it under the negated condition. The compiler accepts the program only if it removes the call, so Click requires the call to be unreachable: the check fails on any path that reaches it. The declaration is visible until its block ends and executes nothing. `sizeof` of an expression does not evaluate its operand.

```c filename=c_compiletime_assert_declaration.c
int32 store(int *cell, int32 value) {
    __attribute__((__noreturn__)) extern void __compiletime_assert_1(void) __attribute__((__error__("Unsupported access size.")));
    if (!((sizeof(*cell) == sizeof(char) || sizeof(*cell) == sizeof(short) || sizeof(*cell) == sizeof(int) || sizeof(*cell) == sizeof(long)) || sizeof(*cell) == sizeof(long long)))
        __compiletime_assert_1();
    *cell = value;
    return *cell;
}

int32 guarded(int32 value) {
    __attribute__((__noreturn__)) extern void __compiletime_assert_1(void) __attribute__((__error__("Unsupported access size.")));
    if (value)
        __compiletime_assert_1();
    return value;
}
```

```click
verifying "c_compiletime_assert_declaration.c";

int32 store(int32* cell, int32 value) {
    owns cell[0..1];
    ensures result == value by auto;
}

int32 guarded(int32 value) {
    requires value == 0;
    ensures result == 0 by auto;
}
```

```expect
pass
```
