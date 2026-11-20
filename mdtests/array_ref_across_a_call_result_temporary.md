# Array reads across a call whose result is built in a temporary

A by-value struct result is built in a fresh temporary before it is copied
into its local. Declaring that temporary writes no caller array, so a pure
function's array argument read before the call is the same version after it,
and the fact is still known. (Adler's `let mut h = Adler32::new();` then
`h.write_slice(data);`.)

```c filename=keep_result.c
struct pair { int32 a; int32 b; };

struct pair make(void) {
    struct pair p = { 1, 0 };
    return p;
}

int32 keep(int32 a[]) {
    struct pair h = make();
    return a[0] + h.a - 1;
}
```

```click
verifying "keep_result.c";
function total(a: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(a[k]) })
}
struct pair make() {
    ensures result.a == 1;
    ensures result.b == 0;
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
    have total(a, 0, 0) == 0 by { known(); }
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
