# an unplaced store does not initialize an unwritten heap element

Fresh `malloc` storage records which of its bytes a store has initialized,
and a store the facts cannot place keeps the marks of the elements it may
alias (a store never de-initializes). The marks it keeps are the ones earlier
stores made, and only those. `a[u] = 7` under `0 <= u < 2` writes `a[1]`
only when `u == 1`, so `a[1]` may still be fresh storage, and reading it is a
read of uninitialized storage.

```c filename=an_unplaced_store_does_not_initialize_an_unwritten_heap_element.c
int32 unwritten_neighbour(int32 u) {
    int32* a = malloc(8);
    int32 r;
    if (a == 0) {
        return 5;
    }
    a[0] = 5;
    a[u] = 7;
    r = a[1];
    free(a);
    return r;
}
```

```click
verifying "an_unplaced_store_does_not_initialize_an_unwritten_heap_element.c";

int32 unwritten_neighbour(int32 u) {
    requires 0 <= u;
    requires u < 2;
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: undefined behavior: read of uninitialized storage
```
