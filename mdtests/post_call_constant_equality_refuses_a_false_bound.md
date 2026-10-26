# A retained post-call equality cannot prove a false bound

The call establishes g == 11, which does not imply g > 11.

```c filename=global.c
int g;
int bumpg(void) { g = g + 1; return 0; }
int h(void) { int a = bumpg(); return a; }
```

```click
verifying "global.c";
int bumpg() {
    requires g < 1000;
    owns g;
    ensures result == 0;
    ensures g == old(g) + 1;
}
int h() {
    requires g == 10;
    owns g;
    ensures result == 0;
} by {
    step(); step();
    have g > 11;
    execute(); solve();
}
```

```expect
fail: could not establish `g > 11`
```
