# Unmodified local reads across control boundaries

The selected field stays equal to the marked read through a join whose
arms write a sibling field, a call that writes a separate object, and
an arbitrary loop iteration that maintains the field in its invariant.

```c filename=boundaries.c
struct Pair { int32 left; int32 right; };

void overwrite(int32* p) { *p = 9; }

int32 joined(int32 value, int32 selector) {
    struct Pair box;
    box.left = value;
    if (selector == 0) {
        box.right = 1;
    } else {
        box.right = 2;
    }
    return box.left;
}

int32 called(int32 value) {
    struct Pair box;
    struct Pair target;
    box.left = value;
    target.left = 0;
    overwrite(&target.left);
    return box.left;
}

int32 looped(int32 value, int32 selector) {
    struct Pair box;
    struct Pair target;
    box.left = value;
    while (selector == 0) {
        target.left = 9;
        break;
    }
    return box.left;
}
```

```click
verifying "boundaries.c";

void overwrite(int32* p) {
    owns p[0..1];
    ensures *p == 9;
}

int32 joined(int32 value, int32 selector) {
    ensures result == value;
} by {
    step(); step();
    mark saved;
    branch ensuring { fact 1 == 1; } {
        true => { step(); }
        false => { step(); }
    }
    have box.left == at(saved, box.left) by known();
    step();
    solve();
}

int32 called(int32 value) {
    ensures result == value;
} by {
    step(); step(); step(); step();
    mark saved;
    step();
    have box.left == at(saved, box.left) by known();
    step();
    solve();
}

int32 looped(int32 value, int32 selector) {
    ensures result == value;
} by {
    step(); step(); step();
    mark saved;
    loop {
        decreases 0;
        invariant box.left == value;
        initialize by solve();
        maintain by {
            have box.left == at(saved, box.left) by known();
            step(); step();
        }
    }
    have box.left == at(saved, box.left) by known();
    step();
    solve();
}
```

```expect
pass
```
