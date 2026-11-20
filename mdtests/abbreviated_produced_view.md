# A produced view can keep its unique direct input borrowed until release

```c filename=short_first.c
int *first(int *left, int *right) { return left; }

int use(void) {
    int a = 1;
    int b = 2;
    int *p = first(&a, &b);
    b = 7;
    int value = *p;
    a = 9;
    return value + a + b;
}
```

```click
verifying "short_first.c";

int32* first(int32* left, int32* right) {
    views left[0..1];
    views *right;
    produces view(*left);
    ensures result == left;
}

int32 use() {
    ensures result == 17;
} by {
    step_until(statement(5).entry);
    release_view(*p);
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
