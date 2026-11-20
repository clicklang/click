# A write through the original name is blocked by the produced view

```c filename=first.c
int *first(int *left, int *right) { return left; }

int use(void) {
    int a = 1;
    int b = 2;
    int *p = first(&a, &b);
    a = 9;
    return *p;
}
```

```click
verifying "first.c";

int32* first(int32* left, int32* right) {
    views *left as left_input;
    views *right;
    produces view(*left) from left_input;
    ensures result == left;
}

int32 use() {
    ensures result == 9;
} by {
    step();
    step();
    step();
    step();
}
```

```expect
fail: write ownership required; available `views a[0..1]` covers the requested range but permits reading only
```
