# unfold of an unheld resource adds no body facts

`get` owns only `p[0..1]`, the one piece `five(p)` contains, not `five(p)`
itself. Holding the pieces does not establish the body's `fact p[0] == 5`,
so `unfold(five(p))` must not add it; otherwise the false
`ensures result == 5` would verify.

```c filename=unfold_of_an_unheld_resource_adds_no_body_facts.c
int get(int *p) { return p[0]; }
```

```click
verifying "unfold_of_an_unheld_resource_adds_no_body_facts.c";

resource five(p: int32*) {
    owns p[0..1];
    fact p[0] == 5;
}

int32 get(int32* p) {
    owns p[0..1];
    ensures result == 5;
} by {
    unfold(five(p));
    execute();
    simp();
}
```

```expect
fail: its pieces are held, but its fact `p[0] == 5` is not established
```
