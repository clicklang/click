# A guard store's footprint excludes iterated ownership bookkeeping

Taking an element and changing its guard retires the taken-out marker. That
ownership-map edit does not write an unrelated pointer cell. The guard write
itself remains in the footprint.

```c filename=iterated_footprint.c
void claim(int *data, int *occupied, int **kept) { occupied[0] = 1; }
```

```click
resource available(data: int32*, occupied: int32*) {
    owns occupied[0..1];
    forall (k: int32) where 0 <= k and k < 1 {
        if occupied[k] == 0 { owns data[k..k + 1]; }
    }
}
verifying "iterated_footprint.c";
void claim(int32 *data, int32 *occupied, int32 **kept) {
    owns available(data, occupied);
    owns kept[0..1];
    produces data[0..1];
    requires occupied[0] == 0;
    ensures kept[0] == old(kept[0]);
} by {
    unfold(available(data, occupied));
    have separate(memory(occupied[0]), memory(kept[0]));
    take(data[0..1]);
    mark before;
    step();
    have separate(statement(0).footprint, memory(kept[0])) by {
        normalize() using { separate(memory(occupied[0]), memory(kept[0])); };
    }
    have kept[0] == at(before, kept[0]) by {
        transport_certificate {
            premise 0: separate(statement(0).footprint, memory(kept[0]))
                => separate(statement(0).footprint, memory(kept[0]));
            preserve 0 => kept[0] == at(before, kept[0]);
            conclusion 1;
        }
    }
    fold(available(data, occupied));
    step();
}
```

```expect
pass
```
