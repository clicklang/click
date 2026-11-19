# A local assignment leaves a viewed array element unchanged

The assignment writes only the fresh local. The read of the viewed array
element is unchanged, so `known()` inside the `have` can use the entry fact
directly.

```c filename=t.c
int32 keep(int32 p[3]) {
    int32 local;
    local = 0;
    return local;
}
```

```click
verifying "t.c";
int32 keep(int32 p[3]) {
    views p[0..3];
    requires p[0] == 5;
    ensures p[0] == 5;
} by {
    step();
    step();
    have p[0] == 5 by { known(); }
}
```

```expect
pass
```
