# A file-scope inferred array takes designators

A designator positions the next initializer, so `{[1] = 2, 5}` sets elements
1 and 2. The bound is one past the largest initialized index, `3`, and
element 0, which no initializer names, is zero (C11 6.7.9p22).

```c filename=designated_global.c
int32 designated[] = {[1] = 2, 5};

int32 sum() {
    return designated[0] + designated[1] + designated[2];
}

unsigned long bytes() {
    return sizeof(designated);
}
```

```click
verifying "designated_global.c";

int32 sum() {
    requires designated[0] == 0 and designated[1] == 2 and designated[2] == 5;
    ensures result == 7;
} by {
    execute();
    simp();
}

uint64 bytes() {
    ensures result == 12;
} by {
    execute();
    simp();
}
```

```expect
pass
```
