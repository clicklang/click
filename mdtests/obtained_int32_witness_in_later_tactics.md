# An `obtain`ed int32 witness is in scope for every later tactic

`let k = obtain(exists (k: int32) { k > x });` names the witness of an established existential
for the rest of the proof block. Later `have` goals and `instantiate` arguments
can read `k`. A quantifier that binds the same name inside a later proposition
keeps its own binder. In the last theorem, instantiation establishes `false`
from opposite comparison facts about `k`, and `close()` uses it.

```click
theorem instantiate_at_the_witness(x: int32) {
    requires exists (k: int32) { k > x };
    requires forall (j: int32) { j > x implies x < 1000 };
    ensures x < 1000 by {
        let k = obtain(exists (k: int32) { k > x });
        instantiate(forall (j: int32) { j > x implies x < 1000 }, k);
        close();
    }
}

theorem quantifier_binder_shadows_the_witness(x: int32) {
    requires exists (k: int32) { k > x };
    requires forall (k: int32) { k > x implies x < 1000 };
    ensures x < 1000 by {
        let k = obtain(exists (k: int32) { k > x });
        instantiate(forall (k: int32) { k > x implies x < 1000 }, k);
        close();
    }
}

theorem two_witnesses_reach_a_contradiction(x: int32) {
    requires exists (k: int32) { k > x };
    requires exists (m: int32) { m < x };
    requires forall (j: int32) { j > x implies j <= x };
    ensures 0 == 1 by {
        let k = obtain(exists (k: int32) { k > x });
        let m = obtain(exists (m: int32) { m < x });
        have k > x by close();
        have m < x by close();
        instantiate(forall (j: int32) { j > x implies j <= x }, k);
        close();
    }
}
```

```expect
pass
```
