# A leak at a return names the return statement

The allocation is still live when the second `return` leaves the function.
The refusal belongs to that whole path, not to one stepped statement, so it
names the statement the path ended at: the `return` a reader has to free
before.

```c filename=leak_at_return.c
struct item {
    int32 value;
};

int32 leak_at_return() {
    struct item* item = malloc(sizeof(struct item));
    if (item == 0) {
        return -1;
    }
    item->value = 1;
    return 0;
}
```

```click
verifying "leak_at_return.c";

int32 leak_at_return() {
    ensures result == -1 or result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: C statement at leak_at_return.c:11:5: `return 0;`
```
