# an implicit zero of an automatic struct array is not another value

An automatic array of structs declared with an initializer is zero in every
field the initializer leaves out, in the elements it lists and in the ones it
does not. Each implicit zero reads as exactly zero, so a claim that one holds
anything else is refused.

```c filename=an_implicit_zero_of_an_automatic_struct_array_is_not_another_value.c
struct node {
    int32 key;
    int32 count;
};

int32 read(void) {
    struct node items[100000] = {{4}};
    return items[0].count + items[99999].key;
}
```

```click
verifying "an_implicit_zero_of_an_automatic_struct_array_is_not_another_value.c";

int32 read() {
    ensures result == 4;
} by {
    execute();
    simp();
}
```

```expect
fail: left side evaluated to 0, right side evaluated to 4
```
