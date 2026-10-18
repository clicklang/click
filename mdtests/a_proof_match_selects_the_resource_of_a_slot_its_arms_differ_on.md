# A proof `match` selects the resource of a slot the parent's arms differ on

`root`'s slot `k` is a `cellA` in arm `A` and a `cellB` in arm `B`. Inside the
proof's `match r.sel` arm `Sel::A`, the unfold of `r` takes its arm `A`, so
`kk` is a `cellA` and `kk.v` reads its field. Before, the slot fixed no
resource for `kk`, `kk.v` was read as `root`'s own field `v`, and the true
claim was refused.

```c filename=a_proof_match_selects_the_resource_of_a_.c
void f(int32* q) { }
```

```click
verifying "a_proof_match_selects_the_resource_of_a_.c";

spec enum Sel { A, B }

resource cellA(p: int32*) {
    field v: int32;
    owns p[0..1];
    fact p[0] == v;
}

resource cellB(p: int32*) {
    field w: int32;
    field v: int32;
    owns p[0..1];
    fact p[0] == v;
    fact w == 0;
}

resource root(q: int32*) {
    field sel: Sel;
    field v: int32;
    field u: int32;
    match sel {
        Sel::A => {
            owns k: cellA(q);
            fact k.v == u;
        },
        Sel::B => {
            owns k: cellB(q);
            fact k.v == u;
            fact k.w == v;
        },
    }
}

void f(int32* q) {
    owns r: root(q);
    requires r.sel != Sel::B;
    requires r.v == 3;
    requires r.u == 4;
} by {
    match r.sel {
        Sel::A => {
            let { k: kk } = unfold(r);
            have kk.v == 4 by { simp(); }
            execute();
            let r = fold(root(q), { sel: Sel::A, v: 3, u: 4 }, { k: kk });
            simp();
        },
        Sel::B => { contradiction(r.sel == Sel::B); },
    }
}
```

```expect
pass
```
