# An inferred bound does not change initialized values

```c filename=bad.c
int bad(void) {
    int values[] = { 10, 20 };
    return values[1];
}
```

```click
verifying "bad.c";
int32 bad() { ensures result == 0; }
```

```expect
fail: unclosed goal
```
