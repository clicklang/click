# A mirrored theorem conclusion closes a function-outcome goal

```c filename=apply_order.c
int32 first(int32 x, int32 y) { return x; }
```

```click
theorem ordered(x: int32, y: int32) {
    requires x < y;
    ensures x < y by assumption();
}
verifying "apply_order.c";
int32 first(int32 x, int32 y) {
    requires x < y;
    ensures y > result;
} by {
    execute();
    have y > result by {
        apply(ordered(x, y)) using { x < y; }
    }
    assumption();
}
```

```expect
pass
```
