# symbolic max verifies on both branches

This checks that the omitted proof verifies an `ensures` clause across every symbolic
branch, using execution-derived pure facts from the `if`.

```c filename=max.c
int32 max(int32 a, int32 b) {
    if (a < b) {
        return b;
    } else {
        return a;
    }
}
```

```click
verifying "max.c";

int32 max(int32 a, int32 b) {
    ensures result >= a;
    ensures result >= b;
}
```

```expect
pass
```
