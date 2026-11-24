# Explicit complete-pointer preservation retains dereference authority

```c filename=pointer_origin.c
int32 read_after_write(int32** slot, int32* target, int32* other) {
    *other = 1;
    return **slot;
}
```

```click
verifying "pointer_origin.c";
int32 read_after_write(int32** slot, int32* target, int32* other) {
    owns *slot;
    owns *target;
    owns *other;
    requires *slot == target;
    requires *target == 7;
    ensures result == 7;
} by {
    have separate(memory(*other), memory(*slot)) by { close(); }
    have separate(memory(*other), memory(*target)) by { close(); }
    mark before;
    step();
    have separate(statement(0).footprint, memory(*slot)) by {
        close() using { separate(memory(*other), memory(*slot)); };
    }
    have separate(statement(0).footprint, memory(*target)) by {
        close() using { separate(memory(*other), memory(*target)); };
    }
    have *slot == at(before, *slot) by {
        preserve(memory(*slot), statement(0));
    }
    have *slot == target by {
        close() using { *slot == at(before, *slot); at(before, *slot) == target; };
    }
    have *target == at(before, *target) by {
        preserve(memory(*target), statement(0));
    }
    have *target == 7 by {
        close() using { *target == at(before, *target); at(before, *target) == 7; };
    }
    step();
}
```

```expect
pass
```
