# A produced view keeps its named input borrowed until release

```c filename=first.c
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
verifying "first.c";

int32* first(int32* left, int32* right) {
    views *left as left_input;
    views *right;
    produces view(*left) from left_input;
    ensures result == left;
}

int32 use() {
    ensures result == 17;
} by {
    step_until(statement(5).entry);
    release_view(*p);
    step_until(function.exit);
    close();
}
```

```expect
pass
```
