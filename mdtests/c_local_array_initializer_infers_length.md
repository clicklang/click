# Infer a local array's length from its initializer

```c filename=array.c
int second(void) {
    int values[] = { 10, 20 };
    return values[1];
}
```

```click
verifying "array.c";
int32 second() { ensures result == 20; }
```

```expect
pass
```
