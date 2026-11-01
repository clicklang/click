# Explicit pointer round trips across a separate store

```c filename=round_trip.c
void change(int32* other) { *other = 7; }
struct Pair { int32 first; int32 second; };
struct Holder { unsigned long word; };
int32 exact(struct Pair* pair, struct Holder* h, int32* other) {
    h->word = (unsigned long)&pair->first;
    change(other);
    return *((int32*)h->word);
}
int32 tagged(struct Pair* pair, struct Holder* h, int32* other) {
    h->word = ((unsigned long)&pair->first) | 1UL;
    change(other);
    return *((int32*)(h->word & ~1UL));
}
```

```click
verifying "round_trip.c";
void change(int32* other) { owns *other; }
int32 exact(struct Pair* pair, struct Holder* h, int32* other) {
    views pair->first;
    owns h->word;
    owns *other;
    requires separate(memory(h->word), memory(*other));
    ensures result == pair->first;
} by {
    step();
    have (h->word as (int32*)) == &pair->first by { normalize(); }
    mark saved;
    step();
    have (h->word as (int32*)) == at(saved, (h->word as (int32*))) by { assumption(); }
    have (h->word as (int32*)) == &pair->first by {
        rewrite((h->word as (int32*)) == at(saved, (h->word as (int32*))));
        assumption();
    }
    step();
}
int32 tagged(struct Pair* pair, struct Holder* h, int32* other) {
    views pair->first;
    owns h->word;
    owns *other;
    requires aligned(&pair->first, 4);
    requires separate(memory(h->word), memory(*other));
    ensures result == pair->first;
} by {
    step();
    have ((h->word & ~1u64) as (int32*)) == &pair->first by { normalize(); }
    mark saved;
    step();
    have ((h->word & ~1u64) as (int32*)) == at(saved, ((h->word & ~1u64) as (int32*))) by { assumption(); }
    have ((h->word & ~1u64) as (int32*)) == &pair->first by {
        rewrite(((h->word & ~1u64) as (int32*)) == at(saved, ((h->word & ~1u64) as (int32*))));
        assumption();
    }
    step();
}
```

```expect
pass
```
