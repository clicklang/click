# A loop body store past its array names the loop and the index bound

The loop runs `i` up to `4`, so its last iteration stores to `items[4]`, one
past the end. The refused store is one Click steps over itself while it
preserves the invariants through the body, so the refusal names the `loop`
tactic and that phase rather than the claim's first tactic, and it states the
missing bound over `i` with the facts about `i` it consulted.

```c filename=loop_body_store_past_its_array.c
int32 fill_too_many() {
    int32 items[4];
    int32 i;
    i = 0;
    while (i < 5) {
        items[i] = 7;
        i = i + 1;
    }
    return 0;
}
```

```click
verifying "loop_body_store_past_its_array.c";

int32 fill_too_many() {
    ensures result == 0;
} by {
    step(); step(); step();
    loop { decreases 5 - i; invariant i >= 0; invariant i <= 4; }
    execute(); simp();
}
```

```expect
fail: could not show `0 <= i && i < 4` from the facts `i <= 4`, `i >= 0`
```
