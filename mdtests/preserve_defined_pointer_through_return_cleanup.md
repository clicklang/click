# A pointer read stays defined through return cleanup

```c filename=return_two_local_cleanups.c
void inspect(int32 **link) {
    int32 first;
    int32 second;
}
```

```click
verifying "return_two_local_cleanups.c";

void inspect(int32** link) {
    views *link;
} by {
    step();
    step();
    have defined(*link) by close();
    step();
    have separate(region(2).footprint, memory(*link)) by close();
    have defined(*link) by { preserve(memory(*link), region(2)); }
    close();
}
```

```expect
pass
```
