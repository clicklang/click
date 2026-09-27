# a requirement reads a file-scope array at its element width

A `requires` clause over a file-scope array reads the element the C program
reads. `bytes[6]` of a `uint8 bytes[8]` is the byte at offset 6, and of an
`int64 words[8]` the eight bytes at offset 48, exactly as the `return` and the
`ensures` clauses read them.

`requires` used to elaborate over an empty state, where no file-scope array is
declared, so every such element fell back to an `int32` load: `bytes[6]` read
four bytes at offset 24. The requirement then constrained a cell nothing else
reads, and a function returning the element it had just required could not
prove it returned that value. `int32` arrays were unaffected, which is how the
gap hid.

The negative twin is
[`a_requirement_on_one_file_scope_element_says_nothing_of_its_neighbor.md`](a_requirement_on_one_file_scope_element_says_nothing_of_its_neighbor.md).

```c filename=a_requirement_reads_a_file_scope_array_at_its_element_width.c
uint8 bytes[8];
int16 halves[8];
int64 words[8];
uint32 units[8];

uint8 get_byte() {
    return bytes[6];
}

int16 get_half() {
    return halves[6];
}

int64 get_word() {
    return words[6];
}

uint32 get_unit() {
    return units[6];
}
```

```click
verifying "a_requirement_reads_a_file_scope_array_at_its_element_width.c";

uint8 get_byte() {
    requires bytes[6] == 4;
    ensures result == 4 by auto;
}

int16 get_half() {
    requires halves[6] == 4;
    ensures result == 4 by auto;
}

int64 get_word() {
    requires words[6] == 4;
    ensures result == 4 by auto;
}

uint32 get_unit() {
    requires units[6] == 4;
    ensures result == 4 by auto;
}
```

```expect
pass
```
