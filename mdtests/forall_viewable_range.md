# Guarded universal range viewability

```c filename=forall_loadable_range.c
int32 range_probe(uint8 bytes[], int32 len) {
    return need_cells(bytes, len);
}
```

```click
verifying "forall_loadable_range.c";

extern int32 need_cells(uint8 bytes[], int32 len) {
    requires forall (k: int32) {
        0 <= k and k < len implies viewable(bytes[k..k + 1])
    };
    ensures result == 0;
}

int32 range_probe(uint8 bytes[], int32 len) {
    requires viewable(bytes[0..len + 1]);
    ensures result == 0 by {
        step(need_cells) by {
            intro();
            intro();
            have k <= k + 1 by { solve() using { 0 <= k; k < len; }; }
            have k + 1 <= len + 1 by { solve() using { 0 <= k; k < len; }; }
            have contains(memory(bytes[0..len + 1]), memory(bytes[k..k + 1])) by {
                apply(click::separation::contains_subrange(bytes, 0, len + 1, k, k + 1));
            }
            apply(click::separation::viewable_restrict(memory(bytes[0..len + 1]), memory(bytes[k..k + 1])));
        }
        step();
        known();
    }
}
```

```expect
pass
```
