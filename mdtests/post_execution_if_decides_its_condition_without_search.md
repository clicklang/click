# A post-execution `if` decides its condition on each outcome path

After `execute()`, an `if` over a stable condition picks one arm per outcome
path. Each path decides `old(b) < old(a)` by exact lookup or by the kernel's
condition decision, here from the C condition the path took, without
searching the proof context.

```c filename=pick_decided.c
int32 pick(int32 a, int32 b) {
    if (a > b) {
        return a;
    }
    return b;
}
```

```click
verifying "pick_decided.c";

int32 pick(int32 a, int32 b) {
    ensures result >= a;
} by {
    execute();
    if old(b) < old(a) {
        have result == a;
    } else {
        have result == b;
    }
}
```

```expect
pass
```
