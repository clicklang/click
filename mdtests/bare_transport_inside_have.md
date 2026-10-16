# A bare `transport` inside a `have` selects its premises

The bare `transport(P, Q)` selects its own frame evidence. Inside a `have`
opened on an execution frontier it does so exactly as between top-level steps:
the source-local candidates first, then the premise planner over the frontier
the `have` was opened on. Here the source itself is the selected premise, and
the expansion writes `transport(...) using { at(function.entry, p[0] == 5); }`.

```c filename=t.c
int32 keep(int32 p[3]) {
    int32 local;
    local = 0;
    return local;
}
```

```click
verifying "t.c";
int32 keep(int32 p[3]) {
    views p[0..3];
    requires p[0] == 5;
    ensures p[0] == 5;
} by {
    step();
    step();
    have p[0] == 5 by {
        transport(at(function.entry, p[0] == 5), p[0] == 5);
    }
    execute();
    simp();
}
```

```expect
pass
```
