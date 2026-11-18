# A loop head proves separation from a live view

The loop inherits the checked write range for `target`. Its entry proof
separates that range from the live view, which remains readable after the loop.

```c filename=loop_head_write_separation.c
int write_and_read(int *target, const int *viewed, int count) {
    int i;
    i = 0;
    while (i < count) {
        *target = 7;
        i = i + 1;
    }
    return *viewed;
}
```

```click
verifying "loop_head_write_separation.c";

int32 write_and_read(int32* target, const int32* viewed, int32 count) {
    requires count >= 0;
    owns target[0..1];
    views viewed[0..1];
    requires separate(memory(target[0..1]), memory(viewed[0..1]));
    ensures result == old(viewed[0]);
} by {
    step();
    step();
    have separate(memory(target[0..1]), memory(viewed[0..1])) by { known(); }
    loop {
        invariant i >= 0 and i <= count;
        decreases count - i;
    }
    step();
}
```

```expect
pass
```
