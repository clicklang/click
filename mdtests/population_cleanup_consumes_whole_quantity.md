# Cleanup consumes the whole quantity after exposing its control

After the unchanged C reset, three members are created under explicit empty
authority and packaged with their counter in an ordinary control. Exposing
the control and consuming the whole batch returns the original counter memory
and borrowed authority with no members left.

```c filename=partial_cleanup.c
struct counter { unsigned int value; };
unsigned int cleanup(struct counter* p) { p->value = 0u; return p->value; }
```

```click
verifying "partial_cleanup.c";
authorized resource remaining(p: struct counter*) {}
resource control(p: struct counter*) {
    owns authority(remaining(p));
    owns p->value;
    fact p->value == 3 - count(remaining(p));
}
uint32 cleanup(struct counter* p) {
    owns p->value;
    owns authority(remaining(p));
    requires count(remaining(p)) == 0;
} by {
    step();
    fold(3 of remaining(p));
    fold(control(p));
    unfold(control(p));
    unfold(3 of remaining(p));
    step();
    simp();
}
```

```expect
pass
```
