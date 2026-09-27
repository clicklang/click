# a long global array keeps the elements a store or a loop misses

A function's entry names every element of a global array it knows nothing
about as one run of cells, whatever the array's length. A store into one
element leaves every other element's entry value, near it and at the far
end, and a loop that writes only another global keeps them all.

```c filename=a_long_global_array_frames_the_elements_a_store_misses.c
int32 buf[1000];
int32 other[4];

void write_one() {
    buf[1] = 7;
}

int32 clear_other_then_read(int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        other[i] = 0;
        i = i + 1;
    }
    return buf[7];
}
```

```click
verifying "a_long_global_array_frames_the_elements_a_store_misses.c";

void write_one() {
    owns buf[1..2];
    ensures buf[1] == 7;
    ensures buf[0] == old(buf[0]);
    ensures buf[2] == old(buf[2]);
    ensures buf[999] == old(buf[999]);
} by { execute(); simp(); }

int32 clear_other_then_read(int32 n) {
    owns other[0..4];
    requires buf[7] == 3;
    requires 0 <= n;
    requires n <= 4;
    ensures result == 3;
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
    }
    step();
    simp();
}
```

```expect
pass
```
