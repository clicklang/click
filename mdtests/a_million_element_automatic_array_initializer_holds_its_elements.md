# a million-element automatic array initializer holds its elements

An automatic array declared with an initializer is zero wherever the
initializer does not write (C11 6.7.9p21). The declaration used to store
every element one by one, so `int32 buf[1000000] = {1, 2, 3};` cost a million
stores and a million statements. The declaration now zero-fills the array as
one run per scalar field of an element, and only the elements the
initializer writes are stored after it.

Here a scalar array and an array of structs read written elements, untouched
elements and fields, a null pointer field, a nested struct's field, and an
element stored over after the declaration.

```c filename=a_million_element_automatic_array_initializer_holds_its_elements.c
struct point {
    int32 x;
    int32 y;
};

struct node {
    int32 key;
    struct node *next;
    struct point at;
};

int32 sum(void) {
    int32 buf[1000000] = {1, 2, 3};
    struct node items[100000] = {{4}, {5, 0, {6, 7}}};
    buf[7] = 9;
    items[99999].key = 10;
    int32 empty = items[1].next == 0;
    return buf[2] + buf[7] + buf[999999] + items[0].key + items[1].at.y + items[0].at.x
        + items[99999].key + items[99998].key + empty;
}
```

```click
verifying "a_million_element_automatic_array_initializer_holds_its_elements.c";

int32 sum() {
    ensures result == 34;
} by {
    execute();
    simp();
}
```

```expect
pass
```
