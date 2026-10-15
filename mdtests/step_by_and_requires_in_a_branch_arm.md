# `step(...) by` and `requires` entries in a `branch` arm

A step written with the proof of its open obligation is checked inside a
`branch` arm as at the top of a claim: `memcmp` owes the definedness of the
bytes it reads, which the `by` body or the `requires` entry proves.

```c filename=step_by_in_a_branch_arm.c
int32 compare_by(uint8 bytes[], int32 c) {
    if (c > 0) {
        return memcmp(bytes, bytes, 2);
    }
    return 0;
}
int32 compare_requires(uint8 bytes[], int32 c) {
    if (c > 0) {
        return memcmp(bytes, bytes, 2);
    }
    return 0;
}
```

```click
verifying "step_by_in_a_branch_arm.c";

int32 compare_by(uint8 bytes[], int32 c) {
    requires viewable(bytes[0..2]);
    ensures 1 == 1 by {
        branch then {
            step() by { simp(); }
            step();
            simp();
        } else {}
        step();
        simp();
    }
}

int32 compare_requires(uint8 bytes[], int32 c) {
    requires viewable(bytes[0..2]);
    ensures 1 == 1 by {
        branch then {
            step() {
                requires forall (k: uint64) { k < 2 implies defined(bytes[k]) and defined(bytes[k]) } by simp;
            }
            step();
            simp();
        } else {}
        step();
        simp();
    }
}
```

```expect
pass
```
