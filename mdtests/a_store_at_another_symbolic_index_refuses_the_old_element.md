# a store at another symbolic index refuses the old element

A store at symbolic index `j` may name the same element as a later read at
symbolic index `i`, so the read cannot be the element's entry value: when
`i == j` the function returns 5. Claiming it returns `old(words[i])` is
refused with an unclosed goal rather than accepted. This catches a store that
fails to invalidate the cells a different symbolic index may alias.

```c filename=a_store_at_another_symbolic_index_refuses_the_old_element.c
int32 words[4];

int32 overwrite_then_read(int32 i, int32 j) {
    words[j] = 5;
    return words[i];
}
```

```click
verifying "a_store_at_another_symbolic_index_refuses_the_old_element.c";

int32 overwrite_then_read(int32 i, int32 j) {
    requires 0 <= i;
    requires i < 4;
    requires 0 <= j;
    requires j < 4;
    owns words[0..4];
    ensures result == old(words[i]) by auto;
}
```

```expect
fail: unclosed goal
```
