# a requirement on one file-scope element says nothing of its neighbor

The negative twin of
[`a_requirement_reads_a_file_scope_array_at_its_element_width.md`](a_requirement_reads_a_file_scope_array_at_its_element_width.md).
Reading a requirement at its element's own width must not make it cover
another element: `bytes[6] == 4` is a fact about the byte at offset 6, and the
byte at offset 5 the function returns is unconstrained, so claiming it is 4
is refused.

```c filename=a_requirement_on_one_file_scope_element_says_nothing_of_its_neighbor.c
uint8 bytes[8];

uint8 get_neighbor() {
    return bytes[5];
}
```

```click
verifying "a_requirement_on_one_file_scope_element_says_nothing_of_its_neighbor.c";

uint8 get_neighbor() {
    requires bytes[6] == 4;
    ensures result == 4 by auto;
}
```

```expect
fail: unclosed goal
```
