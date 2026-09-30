# a zero field of a million-element struct array is not one

The fields of an array of structs that its initializer does not write are
runs of zeros at program entry, one per field. An untouched field reads as
exactly zero, so a claim that it holds anything else is refused.

```c filename=a_zero_field_of_a_million_element_struct_array_is_not_one.c
struct node {
    int32 key;
    struct node *next;
};

struct node pool[1000000] = {[3] = {5}};

int main(void) {
    return pool[7].key;
}
```

```click
verifying "a_zero_field_of_a_million_element_struct_array_is_not_one.c";

int main() {
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: left side evaluated to 0, right side evaluated to 1
```
