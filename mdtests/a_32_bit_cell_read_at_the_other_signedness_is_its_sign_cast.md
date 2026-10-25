# a 32-bit cell read at the other signedness is its sign cast

C11 6.5p7 lets an object of type `unsigned int` be read through an `int`
lvalue and the reverse, which GCC and Clang accept through a pointer
conversion. The read returns the stored four bytes in the reader's
signedness, which is C's modular conversion between the two types: rule K5
(`design/machine-integers.md`). So `4294967295u` stored and read through
`int *` is `-1`, and `-1` stored and read through `unsigned *` is
`4294967295`. Reads at the stored signedness are the controls. A cell the
contract states at one signedness (`u[i] == 4294967295u`) reads the same
way through the other, because both reads name one word.

```c filename=a_32_bit_cell_read_at_the_other_signedness_is_its_sign_cast.c
int unsigned_stored_read_signed(void) {
    unsigned cells[1];
    int *s;
    cells[0] = 4294967295u;
    s = (int *)(void *)cells;
    return s[0];
}

unsigned unsigned_stored_read_unsigned(void) {
    unsigned cells[1];
    cells[0] = 4294967295u;
    return cells[0];
}

unsigned signed_stored_read_unsigned(void) {
    int cells[1];
    unsigned *u;
    cells[0] = -1;
    u = (unsigned *)(void *)cells;
    return u[0];
}

int signed_stored_read_signed(void) {
    int cells[1];
    cells[0] = -1;
    return cells[0];
}

int stated_unsigned_read_signed(unsigned *u, int i) {
    int *s;
    s = (int *)(void *)u;
    return s[i];
}
```

```click
verifying "a_32_bit_cell_read_at_the_other_signedness_is_its_sign_cast.c";

int unsigned_stored_read_signed() { ensures result == -1 by auto(); }
unsigned unsigned_stored_read_unsigned() { ensures result == 4294967295u32 by auto(); }
unsigned signed_stored_read_unsigned() { ensures result == 4294967295u32 by auto(); }
int signed_stored_read_signed() { ensures result == -1 by auto(); }

int stated_unsigned_read_signed(unsigned *u, int i) {
    requires i >= 0;
    requires i < 4;
    views u[0..4];
    requires u[i] == 4294967295u32;
    ensures result == -1;
} by {
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
