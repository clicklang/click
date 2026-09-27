# a million-element global array names only the elements it reads

A function's entry holds a global array it knows nothing about as one run of
cells, and an element's entry value gets its load identity when something
first reads that element. Collecting the variables the entry memory mentions
used to name every element instead, so a function over a one-million-element
array minted a million load identities before its first statement and
exhausted the load-variable registry.

Here the function swaps the two end elements through a temporary and returns
a third. The contract relates the swapped ends to their entry values, keeps
the returned element and an untouched one framed, and verifies.

```c filename=a_million_element_global_array_names_only_the_elements_it_reads.c
int32 buf[1000000];

int32 swap_ends() {
    int32 t;
    t = buf[0];
    buf[0] = buf[999999];
    buf[999999] = t;
    return buf[7];
}
```

```click
verifying "a_million_element_global_array_names_only_the_elements_it_reads.c";

int32 swap_ends() {
    owns buf[0..1000000];
    ensures buf[0] == old(buf[999999]);
    ensures buf[999999] == old(buf[0]);
    ensures result == old(buf[7]);
    ensures buf[5] == old(buf[5]);
} by {
    execute();
    simp();
}
```

```expect
pass
```
