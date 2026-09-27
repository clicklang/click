# a million-element initialized array starts as its initializer at program entry

A program's entry knows the initial contents of its static storage. An array
whose initializer writes a few elements and leaves the rest zero used to be
held, and stored at entry, one element at a time, so each of these
declarations cost its declared length in the frontend and again in the
verification of `main`. The unwritten elements are now one run of zeros with
the written ones stored over it.

Here `main` reads written elements, implicit zeros and a stored-over element
of a global array, a file-scope matrix, a static local array and a byte array,
each of a million elements, and `peek` reads a `const` table, whose contents
every function knows.

```c filename=a_million_element_initialized_array_starts_as_its_initializer_at_program_entry.c
int32 buf[1000000] = {1, 2, 7, [999999] = 3};
static int32 grid[1000][1000] = {{4}, {5, 6}};
uint8 bytes[1000000] = {255};
const int32 table[1000000] = {[3] = 4};

int32 peek() {
    return table[3] + table[4];
}

int main(void) {
    static int32 counts[1000000] = {[7] = 5};
    buf[500] = 9;
    return buf[2] + buf[3] + buf[500] + buf[999999] + grid[1][1] + grid[999][999]
        + counts[7] + counts[8] + bytes[0] + bytes[1];
}
```

```click
verifying "a_million_element_initialized_array_starts_as_its_initializer_at_program_entry.c";

int32 peek() {
    ensures result == 4;
} by {
    execute();
    simp();
}

int main() {
    ensures result == 285;
} by {
    execute();
    simp();
}
```

```expect
pass
```
