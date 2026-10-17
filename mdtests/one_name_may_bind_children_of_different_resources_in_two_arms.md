# One name may bind children of different resources in two arms

Each arm of the proof's `match` unfolds `r` and calls its child `x`: a
`cellA` in arm `A`, a `cellB` in arm `B`. A proof name keeps one instance
identity in its declaration, so both arms bind the same identity; each arm
reads `x` as the child it unfolded. Before, the resource the first arm gave
`x` stayed recorded for the second, which was refused with "child `x` is
`cellA`, but slot `m` of `root` owns `cellB`".

```c filename=arms_bind_one_name.c
void f(int32* q) { }
```

```click
verifying "arms_bind_one_name.c";

spec enum Sel { A, B }

resource cellA(p: int32*) {
    field v: int32;
    owns p[0..1];
    fact p[0] == v;
}

resource cellB(p: int32*) {
    field v: int32;
    owns p[0..1];
    fact p[0] == v + 1;
}

resource root(q: int32*) {
    field sel: Sel;
    field u: int32;
    match sel {
        Sel::A => {
            owns k: cellA(q);
            fact k.v == u;
        },
        Sel::B => {
            owns m: cellB(q);
            fact m.v == u;
        },
    }
}

void f(int32* q) {
    owns r: root(q);
} by {
    match r.sel {
        Sel::A => {
            let { k: x, u: ru } = unfold(r);
            have x.v == ru by { simp(); }
            execute();
            let r = fold(root(q), { sel: Sel::A, u: ru }, { k: x });
            simp();
        },
        Sel::B => {
            let { m: x, u: ru } = unfold(r);
            have x.v == ru by { simp(); }
            execute();
            let r = fold(root(q), { sel: Sel::B, u: ru }, { m: x });
            simp();
        },
    }
}
```

```expect
pass
```
