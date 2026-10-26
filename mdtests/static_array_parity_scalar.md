# function-local static arrays keep one stable object

A fixed-size scalar `static` array is initialized once and reused by later
calls, while contracts can authorize and describe its indexed elements.

```c filename=static_local_arrays.c
int32 increment_twice() {
    static int32 values[] = {5, 7, 0};
    values[0] = values[0] + 1;
    values[0] = values[0] + 1;
    return values[0] + values[1] + values[2];
}

int32 call_twice() {
    int32 first;
    int32 second;
    first = increment_twice();
    second = increment_twice();
    return second;
}
```

```click
verifying "static_local_arrays.c" as static_local;

int32 increment_twice() {
    owns values[0..3];
    requires values[0] > -1000 and values[0] < 1000 and values[1] > -1000 and values[1] < 1000 and values[2] > -1000 and values[2] < 1000;
    ensures to_integer(result) == to_integer(old(values[0]) + old(values[1]) + old(values[2]) + 2);
    ensures to_integer(values[0]) == to_integer(old(values[0]) + 2);
    ensures values[1] == old(values[1]);
    ensures values[2] == old(values[2]);
}

int32 call_twice() {
    owns static_local::increment_twice::values[0..3];
    requires static_local::increment_twice::values[0] == 5 and static_local::increment_twice::values[1] == 7 and static_local::increment_twice::values[2] == 0;
    ensures result == 16;
}
```

```expect
pass
```
