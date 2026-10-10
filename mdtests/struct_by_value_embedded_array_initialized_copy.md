# Initialized embedded arrays copied by value

The aggregate-value boundary requires initialized modeled fields, independent
of padding. This positive counterpart to the partial-array refusals exercises
both array dimensions and their complete ABI strides without changing those
original source programs.

```c filename=initialized_embedded_arrays.c
struct point {
    int32 value;
    uint8 flag;
};

struct packet {
    uint8 tag;
    struct point pair[2];
    struct point grid[2][2];
    int32 tail;
};

struct packet finish(struct packet value) {
    struct packet local;
    local = value;
    local.pair[1].value = 7;
    local.grid[1][1].value = 9;
    return local;
}

int32 run_initialized_embedded_arrays() {
    struct packet original;
    struct packet copy;
    original.tag = 8;
    original.pair[0].value = 1;
    original.pair[0].flag = 2;
    original.pair[1].value = 4;
    original.pair[1].flag = 3;
    original.grid[0][0].value = 1;
    original.grid[0][0].flag = 2;
    original.grid[0][1].value = 2;
    original.grid[0][1].flag = 3;
    original.grid[1][0].value = 3;
    original.grid[1][0].flag = 4;
    original.grid[1][1].value = 5;
    original.grid[1][1].flag = 6;
    original.tail = 5;
    copy = finish(original);
    return original.pair[1].value * 1000 + copy.pair[1].value * 100
        + original.grid[1][1].value * 10 + copy.grid[1][1].value;
}
```

```click
verifying "initialized_embedded_arrays.c";

struct packet finish(struct packet value) {
    ensures result.pair[1].value == 7;
    ensures result.grid[1][1].value == 9;
} by {
    auto;
}

int32 run_initialized_embedded_arrays() {
    ensures result == 4759;
} by {
    execute();
    simp();
}
```

```expect
pass
```
