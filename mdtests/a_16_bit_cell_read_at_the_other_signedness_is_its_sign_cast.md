# a 16-bit cell read at the other signedness is its sign cast

C11 6.5p7 lets an object of type `unsigned short` be read through a `short`
lvalue and the reverse, which GCC and Clang accept through a pointer
conversion. The read returns the stored two bytes in the reader's
signedness, which is C's modular conversion between the two types. So
`65535` stored and read through `short *` is `-1`, and `-1` stored and read
through `unsigned short *` is `65535`. Reads at the stored signedness are the
controls. A cell the contract states at one signedness (`u[i] == 65535`)
reads the same way through the other: the equality graph relates the two
reads of one cell by the sign cast, as it does at 8 and 32 bits
(`a_32_bit_cell_read_at_the_other_signedness_is_its_sign_cast.md`).

```c filename=a_16_bit_cell_read_at_the_other_signedness_is_its_sign_cast.c
short unsigned_stored_read_signed(void) {
    unsigned short cells[1];
    short *s;
    cells[0] = 65535;
    s = (short *)(void *)cells;
    return s[0];
}

unsigned short unsigned_stored_read_unsigned(void) {
    unsigned short cells[1];
    cells[0] = 65535;
    return cells[0];
}

unsigned short signed_stored_read_unsigned(void) {
    short cells[1];
    unsigned short *u;
    cells[0] = -1;
    u = (unsigned short *)(void *)cells;
    return u[0];
}

short signed_stored_read_signed(void) {
    short cells[1];
    cells[0] = -1;
    return cells[0];
}

short stated_unsigned_read_signed(unsigned short *u, int i) {
    short *s;
    s = (short *)(void *)u;
    return s[i];
}

unsigned short stated_signed_read_unsigned(short *s, int i) {
    unsigned short *u;
    u = (unsigned short *)(void *)s;
    return u[i];
}
```

```click
verifying "a_16_bit_cell_read_at_the_other_signedness_is_its_sign_cast.c";

int16 unsigned_stored_read_signed() { ensures result == -1; }
uint16 unsigned_stored_read_unsigned() { ensures result == 65535; }
uint16 signed_stored_read_unsigned() { ensures result == 65535; }
int16 signed_stored_read_signed() { ensures result == -1; }

int16 stated_unsigned_read_signed(uint16* u, int32 i) {
    requires i >= 0;
    requires i < 4;
    views u[0..4];
    requires u[i] == 65535;
    ensures result == -1;
} by {
    step_until(function.exit);
    close();
}

uint16 stated_signed_read_unsigned(int16* s, int32 i) {
    requires i >= 0;
    requires i < 4;
    views s[0..4];
    requires s[i] == -1;
    ensures result == 65535;
} by {
    step_until(function.exit);
    close();
}
```

```expect
pass
```
