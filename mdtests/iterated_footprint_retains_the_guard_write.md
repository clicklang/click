# An iterated footprint retains the actual guard write

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
    have separate(statement(0).footprint, memory(occupied[0])) by {
        normalize() using { separate(memory(occupied[0]), memory(kept[0])); };
    }
}
```

```expect
fail: goal did not normalize to true
```
