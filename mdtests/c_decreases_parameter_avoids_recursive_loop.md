# completed numeric descent needs no second source-body check

The ordinary proof follows a concretely false loop condition. Its unreachable
recursive call creates no descent obligation; the live call still must descend.

```c filename=c_decreases_parameter_avoids_recursive_loop.c
int32 countdown(int32 n) {
    if (n > 0) return countdown(n - 1);
    while (0) { countdown(n); }
    return 0;
}
```

```click
verifying "c_decreases_parameter_avoids_recursive_loop.c";

int32 countdown(int32 n) {
    decreases n;
    requires n >= 0;
    ensures result == 0;
}
```

```expect
pass
```
