# An arbitrary integer can name an opaque pointer but cannot grant bounds

Returning the reconstructed value creates no allocation authority. A read
through it still needs an explicit full-pointer relationship and permission.

```c filename=pointer_address_rejects_unrelated_integer.c
struct node {
    int32 value;
    unsigned long word;
};

struct node* forge(unsigned long word) {
    return (struct node*)word;
}
int32 read_forged(unsigned long word) {
    return ((struct node*)word)->value;
}
```

```click
verifying "pointer_address_rejects_unrelated_integer.c";

struct node* forge(unsigned long word) {
    ensures result == result;
} by {
    execute();
    simp();
}
int32 read_forged(unsigned long word) {
    ensures result == result;
} by { execute(); simp(); }
```

```expect
fail: access outside the subobject the pointer designates
```
