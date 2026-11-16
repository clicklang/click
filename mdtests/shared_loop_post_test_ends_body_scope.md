# A switch continue ends body storage before the shared post-test

The inline reader can read a live local, but the array in the loop body has
already left scope when its switch-enclosed continue reaches the post-test.

```c filename=shared_post_test_scope.c
static inline int32 read_cell(int32* p) { return p[0]; }

int32 read_live_body() {
    int32 a[1];
    a[0] = 0;
    return read_cell(a);
}

int32 expired_post_test() {
    int32* q;
    do {
        int32 a[1];
        a[0] = 0;
        q = &a[0];
        switch (0) { default: continue; }
    } while (read_cell(q));
    return 0;
}
```

```click
verifying "shared_post_test_scope.c";

int32 read_live_body() { ensures result == 0; }
int32 expired_post_test() { ensures result == 0; }
```

```expect
fail: invalid memory access
```
