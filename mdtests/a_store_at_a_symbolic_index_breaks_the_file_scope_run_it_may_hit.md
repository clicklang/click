# a store at a symbolic index breaks the file-scope run it may hit

A read at a symbolic index takes the run's load only when every element the
index may name is still one of the run's live cells. A store at another
symbolic index that may be the same element makes those elements holes, so
the read after it cannot be the element's entry value: `i` and `j` may be
equal, and then the function returns 5. Claiming it returns `old(words[i])`
is refused.

See [`a_symbolic_index_reads_a_large_file_scope_array.md`](a_symbolic_index_reads_a_large_file_scope_array.md)
for the read the run does decide.

```c filename=a_store_at_a_symbolic_index_breaks_the_file_scope_run_it_may_hit.c
int32 words[1000];

int32 overwrite_then_read(int32 i, int32 j) {
    words[j] = 5;
    return words[i];
}
```

```click
verifying "a_store_at_a_symbolic_index_breaks_the_file_scope_run_it_may_hit.c";

int32 overwrite_then_read(int32 i, int32 j) {
    requires 0 <= i;
    requires i < 1000;
    requires 0 <= j;
    requires j < 1000;
    owns words[0..1000];
    ensures result == old(words[i]) by auto;
}
```

```expect
fail: unclosed goal
```
