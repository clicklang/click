# sizeof measures the complete array without evaluating its initializer

```c filename=example.c
int answer(void) {
    int count = 0;
    return sizeof((int[]){++count, 20, 30}) + count;
}
```

```click
verifying "example.c";
int32 answer() { ensures result == 12; }
```

```expect
pass
```
