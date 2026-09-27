# a symbolic index reads a large file-scope array

A file-scope array's entry cells are one run: element `k` holds the load of
element `k` at the storage's symbolic base. A read at a symbolic index the
facts place inside the array reads that run as one family, so its value is
the load of the indexed element, which the requirement written over the same
element constrains.

Each element used to be its own cell, and the read asked them one at a time,
splitting off a case per element and recursing into the rest. A thousand
elements overflowed the stack before the first proof step ran.

The negative twin is
[`a_symbolic_index_into_a_large_file_scope_array_reads_only_its_element.md`](a_symbolic_index_into_a_large_file_scope_array_reads_only_its_element.md).

```c filename=a_symbolic_index_reads_a_large_file_scope_array.c
int32 words[1000];
uint8 bytes[4096];
int64 wide[2048];

int32 get_word(int32 i) {
    return words[i];
}

int32 get_next_word(int32 i) {
    return words[i + 1];
}

uint8 get_byte(int32 i) {
    return bytes[i];
}

int64 get_wide(int32 i) {
    return wide[i];
}
```

```click
verifying "a_symbolic_index_reads_a_large_file_scope_array.c";

int32 get_word(int32 i) {
    requires 0 <= i;
    requires i < 1000;
    requires words[i] == 7;
    ensures result == 7 by auto;
}

int32 get_next_word(int32 i) {
    requires 0 <= i;
    requires i < 999;
    requires words[i + 1] == 7;
    ensures result == 7 by auto;
}

uint8 get_byte(int32 i) {
    requires 0 <= i;
    requires i < 4096;
    requires bytes[i] == 7;
    ensures result == 7 by auto;
}

int64 get_wide(int32 i) {
    requires 0 <= i;
    requires i < 2048;
    requires wide[i] == 7;
    ensures result == 7 by auto;
}
```

```expect
pass
```
