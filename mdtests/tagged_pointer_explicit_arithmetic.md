# A tag equality closes by `close() using` its selected premises

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `close() using { ... }`.

```c filename=tagged_pointer_explicit_arithmetic.c
struct node {
    int32 value;
    unsigned long word;
};

unsigned long set_black(unsigned long word, struct node* next) {
    return word | 2;
}
```

```click
verifying "tagged_pointer_explicit_arithmetic.c";

unsigned long set_black(unsigned long word, struct node* next) {
    requires aligned(next, 8);
    requires word == address(next) + 1;
    ensures result == address(next) + 3;
} by {
    step_until(function.exit);
    have result == address(next) + 3 by {
        close() using { word == address(next) + 1; aligned(next, 8); };
    }
    solve();
}
```

```expect
pass
```
