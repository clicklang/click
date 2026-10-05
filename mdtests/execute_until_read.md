# Select an explicit scalar read

`read(N)` selects the zero-based static occurrence of a statement containing
an explicit scalar memory load. Other assignments do not count. It pauses
before that statement; `step()` checks access and performs the load.

```c filename=read.c
int32 loaded(const uint8* p) {
    int32 x;
    int32 other;
    other = 1;
    x = (int32)*p;
    other = 2;
    return x;
}
```

```click
verifying "read.c";
int32 loaded(const uint8* p) {
    views p[0..1];
    ensures 0 <= result and result <= 255;
} by {
    execute_until(read(0));
    step();
    have 0 <= x and x <= 255 by { simp(); }
    execute(); simp();
}
```

```expect
pass
```
