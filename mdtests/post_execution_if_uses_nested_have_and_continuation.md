# Nested post-execution arms and their continuation see earlier facts

```c filename=pick.c
int32 pick(int32 a, int32 b) {
    if (a > b) {
        return a;
    }
    return b;
}
```

```click
verifying "pick.c";

int32 pick(int32 a, int32 b) {
    requires a > b or a == b;
    ensures result >= a;
} by {
    execute();
    if old(a) > old(b) {
        have old(a) >= old(b);
        if old(a) >= old(b) {
            have result == a;
        } else {
            have result == b;
        }
    } else {
        have old(a) >= old(b);
    }
    if old(a) >= old(b) {
        have result >= a;
    } else {
        have result == b;
    }
}
```

```expect
pass
```
