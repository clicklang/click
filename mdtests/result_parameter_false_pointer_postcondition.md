# A typed load cannot switch the C pointer binding

```c filename=select.c
int32 *select(int32 *result, int32 *next) { return next; }
```

```click
verifying "select.c";
int32 *select(int32 *result, int32 *next) {
    views result[0..1];
    views next[0..1];
    requires c(result)[0] == 3 and next[0] == 7;
    ensures load_int32(c(result)) == 7 by auto;
}
```

```expect
fail: unclosed goal
```
