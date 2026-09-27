# long global arrays of several element types read and store a few elements

A function's entry holds each global or static array it knows nothing about
as one run of cells, and names an element's entry value only when something
reads that element. That holds whatever the element type: bytes, 64-bit
integers and pointers are named lazily just as `int32` elements are, and a
function-scope static array is one run too.

`touch` copies one element of a static array into another, stores into a
byte array and a 64-bit array, and returns its argument; `read_pointer` reads
one pointer element. Every array has one hundred thousand elements.

```c filename=long_global_arrays_of_several_element_types_read_and_store_a_few_elements.c
uint8 bytes[100000];
int32* pointers[100000];
int64 wide[100000];

int32 touch(int32 k) {
    static int32 counts[100000];
    counts[3] = counts[4];
    bytes[99999] = 1;
    wide[5] = 7;
    return k;
}

int32 read_pointer() {
    int32* p;
    p = pointers[42];
    return 0;
}
```

```click
verifying "long_global_arrays_of_several_element_types_read_and_store_a_few_elements.c";

int32 touch(int32 k) {
    owns counts[3..4];
    owns bytes[99999..100000];
    owns wide[5..6];
    ensures result == k;
    ensures counts[3] == old(counts[4]);
    ensures bytes[99999] == 1;
    ensures wide[5] == 7;
} by {
    execute();
    simp();
}

int32 read_pointer() {
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
