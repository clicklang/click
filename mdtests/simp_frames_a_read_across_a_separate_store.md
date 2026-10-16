# `simp` carries a read across a store a separation keeps away from it

The last store writes `owner->cell[0]` from `owner->phase`, which a branch
set just before, so the goal reads `owner->phase` twice: once before the
store, as the stored value, and once after it. The separation of `*owner` from
the cell, carried through the branch's `ensuring`, shows the store left
`owner->phase` alone. `simp` proves the goal by `transport` from the read's
reflexive equality at the store's entry, citing that separation as the frame.
The pattern is `examples/perpetual-service`'s `service_step`.

```c filename=simp_frames_a_read_across_a_separate_store.c
struct service {
    int32 phase;
    int32* cell;
};

int32 service_step(struct service* owner) {
    if (owner->phase == 0) {
        owner->phase = 1;
    } else {
        owner->phase = 0;
    }
    owner->cell[0] = owner->phase;
    return owner->phase;
}
```

```click
verifying "simp_frames_a_read_across_a_separate_store.c";

int32 service_step(struct service* owner) {
    requires 0 <= owner->phase;
    requires owner->phase <= 1;
    requires separate(memory(*owner), memory(owner->cell[0..1]));
    owns *owner;
    owns owner->cell[0..1];
    ensures owner->cell[0] == owner->phase;
} by {
    branch ensuring {
        fact owner->cell == old(owner->cell);
        fact separate(memory(*owner), memory(owner->cell[0..1]));
        owns *owner;
        owns owner->cell[0..1];
    } then {
        step();
        have owner->cell == old(owner->cell) by auto();
    } else {
        step();
        have owner->cell == old(owner->cell) by auto();
    }
    step();
    have owner->cell[0] == owner->phase by simp();
    execute();
    simp();
}
```

```expect
pass
```
