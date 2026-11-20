# A global array precondition survives calls that write another object

The final call uses the version of `h` from the caller's entry. Each preceding
call has a checked write footprint in `g`, a distinct global.

```c filename=global_array_precondition_survives_disjoint_calls.c
int32 g[4];
int32 h[4];
void touch_g() { g[0] = 1; }
int32 see_h() { return 0; }
void caller() {
    touch_g();
    touch_g();
    touch_g();
    touch_g();
    see_h();
}
```

```click
verifying "global_array_precondition_survives_disjoint_calls.c";

function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}
void touch_g() { owns g[0..1]; }
int32 see_h() {
    requires icount(h, 0, 1) == 5;
    ensures result == 0;
}
void caller() {
    requires icount(h, 0, 1) == 5;
    owns g[0..1];
    views h[0..1];
} by {
    step();
    step();
    step();
    step();
    step();
}
```

```expect
pass
```
