# A block-scope `error` declaration and its unreachable call

The Linux `compiletime_assert` macro declares, inside a block, an external function with the GNU `error` attribute and calls it under the negated condition. The compiler accepts the program only if it removes the call, so Click requires the call to be unreachable: the check fails on any path that reaches it. The declaration is visible until its block ends and executes nothing. `sizeof` of an expression does not evaluate its operand. `write_once` has the shape the kernel's `WRITE_ONCE` macro expands to.

```c filename=c_compiletime_assert_declaration.c
int32 store(int *cell, int32 value) {
    __attribute__((__noreturn__)) extern void __compiletime_assert_1(void) __attribute__((__error__("Unsupported access size.")));
    if (!((sizeof(*cell) == sizeof(char) || sizeof(*cell) == sizeof(short) || sizeof(*cell) == sizeof(int) || sizeof(*cell) == sizeof(long)) || sizeof(*cell) == sizeof(long long)))
        __compiletime_assert_1();
    *cell = value;
    return *cell;
}

struct node {
    struct node *left;
};

void write_once(struct node *parent, struct node *new) {
    do { do { __attribute__((__noreturn__)) extern void __compiletime_assert_1(void) __attribute__((__error__("Unsupported access size."))); if (!((sizeof(parent->left) == sizeof(char) || sizeof(parent->left) == sizeof(short) || sizeof(parent->left) == sizeof(int) || sizeof(parent->left) == sizeof(long)) || sizeof(parent->left) == sizeof(long long))) __compiletime_assert_1(); } while (0); do { *(volatile typeof(parent->left) *)&(parent->left) = (new); } while (0); } while (0);
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

void write_once(struct node* parent, struct node* new) {
    owns &parent->left;
    ensures parent->left == new by auto;
}

int32 guarded(int32 value) {
    requires value == 0;
    ensures result == 0 by auto;
}
```

```expect
pass
```
