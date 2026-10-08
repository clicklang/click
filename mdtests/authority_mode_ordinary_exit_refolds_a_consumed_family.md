# An ordinary consumes/produces contract refolds its family at exit in authority mode

`box_renew` unfolds the `boxed(box)` it consumes, replaces the allocation,
and returns without an explicit `fold`. Under both resource semantics the
closing `simp` reads the body outcome through the contract's checked
resource transition, which folds the returned `boxed(box)` once the body
holds its pieces.

`boxed` is not `authorized`, so the contract reaches no population. Authority
mode used to refuse that transition for every contract that its population
helper rules did not admit, so the closing reported the produced
`boxed(box)` missing. The refusal now applies only to a contract that
reaches a population, as it already did at call sites.

```c filename=box.c
struct box {
    int32* data;
    int32 tag;
};

void box_renew(struct box* box) {
    int32* fresh;
    fresh = malloc(4);
    if (fresh == 0) {
        return;
    }
    fresh[0] = box->data[0];
    free(box->data);
    box->data = fresh;
}

int32 box_cycle(struct box* box) {
    box_renew(box);
    box_renew(box);
    return box->data[0];
}
```

```click resource_semantics=authority
resource boxed(box: struct box*) {
    owns *box;
    contains allocation(box->data, 4);
    owns box->data[0..1];
    fact separate(memory(*box), memory(box->data[0..1]));
}

verifying "box.c";

void box_renew(struct box* box) {
    consumes boxed(box);
    produces boxed(box);
    ensures box->data[0] == old(box->data[0]);
    ensures box->tag == old(box->tag);
} by {
    unfold(boxed(box));
    execute();
    simp();
}

int32 box_cycle(struct box* box) {
    consumes boxed(box);
    produces boxed(box);
    ensures result == old(box->data[0]);
} by {
    execute();
    simp();
}
```

```expect
pass
```
