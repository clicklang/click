# Return proofs retain definedness without a resource rewrite

These `have` steps establish the arithmetic domain in the outcome proof.
The contract goal consumes that evidence through ordinary obligation checking,
and final certification consumes the completed claim. No resource rewrite or
reconstruction of the proof facts from the C execution trace is needed.
```c filename=return_definedness.c
int32 g[4];

int32 planned(int32 u) {
    int32 r;
    g[u] = 7;
    r = g[0];
    r = r + 1;
    return r;
}
```
```click
verifying "return_definedness.c";

int32 planned(int32 u) {
    requires 0 <= u;
    requires u < 4;
    requires g[0] < 100;
    owns g[0..4];
    ensures result == 8 or to_integer(result) == to_integer(old(g[0]) + 1);
} by {
    step();
    step();
    step();
    if u == 0 {
        step();
        step();
        step();
        have defined(old(g[0]) + 1);
        have result == 8 or defined(old(g[0]) + 1);
        solve();
    } else {
        step();
        step();
        step();
        have defined(old(g[0]) + 1);
        have result == 8 or defined(old(g[0]) + 1);
        solve();
    }
}

```
```expect
pass
```
