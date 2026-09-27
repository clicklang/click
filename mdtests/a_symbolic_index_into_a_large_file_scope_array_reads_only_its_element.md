# a symbolic index into a large file-scope array reads only its element

The negative twin of
[`a_symbolic_index_reads_a_large_file_scope_array.md`](a_symbolic_index_reads_a_large_file_scope_array.md).
Reading the run at a symbolic index gives the load of that element and no
other: a requirement on `words[j]` says nothing of `words[i]` when nothing
ties `i` to `j`, so claiming the read returns the required value is refused.

```c filename=a_symbolic_index_into_a_large_file_scope_array_reads_only_its_element.c
int32 words[1000];

int32 get_word(int32 i, int32 j) {
    return words[i];
}
```

```click
verifying "a_symbolic_index_into_a_large_file_scope_array_reads_only_its_element.c";

int32 get_word(int32 i, int32 j) {
    requires 0 <= i;
    requires i < 1000;
    requires 0 <= j;
    requires j < 1000;
    requires words[j] == 7;
    ensures result == 7 by auto;
}
```

```expect
fail: unclosed goal
```
