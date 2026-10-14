# A guarded ordinary return refold is retained before a named resource exchange

The iterated, field-free `cell` fold changes the returned resource context. The following
named fold must observe that checked context, rather than the context from
before `cell` was refolded. This is the small gate regression for the arena
allocation and shared-heap return-refold failures.

```c filename=refold.c
void inspect(int32* p, int32* occupied) { }
```

```click
verifying "refold.c";
resource cell(p: int32*, occupied: int32*) {
    owns occupied[0..1];
    forall (k: int32) where 0 <= k and k < 1 {
        if occupied[k] == 0 { owns p[k..k + 1]; }
    }
}
resource marker() { field value: int32; }

void inspect(int32* p, int32* occupied) {
    owns cell(p, occupied);
    produces tag: marker();
    ensures tag.value == 1;
} by {
    unfold(cell(p, occupied));
    execute();
    fold(cell(p, occupied));
    let tag = fold(marker(), { value: 1 });
    simp();
}
```

```expect
pass
```
