# Array compound literals initialize on the selected branch and decay to mutable pointers

```c filename=example.c
int answer(void) {
    int count = 0;
    int *values = 1 ? (int[3]){++count, 20} : (int[2]){++count, 99};
    int *last = &values[2];
    *last += 21;
    return count + values[1] + *last;
}
```

```click
verifying "example.c";
int32 answer() { ensures result == 42; }
```

```expect
pass
```
