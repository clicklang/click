# An undecided write guard retains the other call write requirements

```c filename=verified_call_mixed_write_bounds.c
struct cells {
    int first;
    int second;
    int saved;
};

void update(struct cells *p, int enabled);

int read_saved(struct cells *p, int enabled) {
    update(p, enabled);
    return p->saved;
}
```

```click
resource guarded_second(p: struct cells*, enabled: int32) {
    if enabled != 0 {
        owns p->second;
    }
}

verifying "verified_call_mixed_write_bounds.c";

extern void update(struct cells* p, int32 enabled) {
    owns p->first;
    owns guarded_second(p, enabled);
}

int32 read_saved(struct cells* p, int32 enabled) {
    owns p->first;
    owns guarded_second(p, enabled);
    views p->saved;
    requires separate(memory(p->first), memory(p->saved));
    requires separate(memory(p->second), memory(p->saved));
    ensures result == old(p->saved);
} by {
    step() {
        requires separate(memory(p->first), memory(p->saved)) by known();
        requires separate(memory(p->second), memory(p->saved)) by known();
    }
}
```

```expect
pass
```
