# a store into a long global array is what a later read of it sees

A function's entry names every element of a global array it knows nothing
about as one run of cells, whatever the array's length. A store into one
element makes that slot a hole of the run, and the read after it sees the
stored `9`, not the entry value the contract states.

```c filename=a_store_into_a_long_global_array_is_read_back.c
int32 buf[1000];

int32 overwrite_then_read() {
    buf[2] = 9;
    return buf[2];
}
```

```click
verifying "a_store_into_a_long_global_array_is_read_back.c";

int32 overwrite_then_read() {
    requires buf[2] == 5;
    owns buf[2..3];
    ensures result == 5;
} by { execute(); simp(); }
```

```expect
fail: left side evaluated to 9, right side evaluated to 5
```
