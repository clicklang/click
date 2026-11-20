# Array reads across a checked call on a local cell

```c filename=keep.c
void touch(int32* p) { *p = 1; }

int32 keep(int32 a[]) {
    int32 local = 0;
    touch(&local);
    local = 2;
    return a[0];
}
```

```click
verifying "keep.c";
function total(a: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(a[k]) })
}
void touch(int32* p) {
    owns *p;
}
int32 keep(int32 a[]) {
    views a[0..1];
    requires a[0] == 7;
    ensures result == 7;
} by {
    have total(a, 0, 0) == 0 by {
        unfold(total(a, 0, 0));
        normalize();
    }
    step();
    step();
    step();
    step();
    have total(a, 0, 0) == 0 by { known(); }
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
