# A composite's produced view must be covered by its named input

```c filename=wrong_cursor.c
void package(int *p, int *q) {}
```

```click
resource cursor(p: int32*) {
    views *p;
}

verifying "wrong_cursor.c";

void package(int32* p, int32* q) {
    views *p;
    views *q as input;
    produces cursor(p) from input;
} by {
    step_until(function.exit);
    fold(cursor(p));
}
```

```expect
fail: prove that the input view covers the produced view
```
