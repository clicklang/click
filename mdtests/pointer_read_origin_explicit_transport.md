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
    have separate(memory(*other), memory(*slot)) by { assumption(); }
    have separate(memory(*other), memory(*target)) by { assumption(); }
    mark before;
    step();
    have separate(statement(0).footprint, memory(*slot)) by {
        normalize() using { separate(memory(*other), memory(*slot)); };
    }
    have separate(statement(0).footprint, memory(*target)) by {
        normalize() using { separate(memory(*other), memory(*target)); };
    }
    have *slot == at(before, *slot) by {
        transport_certificate {
            premise 0: separate(statement(0).footprint, memory(*slot))
                => separate(statement(0).footprint, memory(*slot));
            preserve 0 => *slot == at(before, *slot);
            conclusion 1;
        }
    }
    have *slot == target by {
        normalize() using { *slot == at(before, *slot); at(before, *slot) == target; };
    }
    have *target == at(before, *target) by {
        transport_certificate {
            premise 0: separate(statement(0).footprint, memory(*target))
                => separate(statement(0).footprint, memory(*target));
            preserve 0 => *target == at(before, *target);
            conclusion 1;
        }
    }
    have *target == 7 by {
        normalize() using { *target == at(before, *target); at(before, *target) == 7; };
    }
    step();
}
```

```expect
pass
```
