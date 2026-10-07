# unfold names its pieces on the left

The pieces a resource opens into are outputs of the step, so they are named
where every other output is: `let { slot: name } = unfold(resource);`. The
trailing `unfold(resource) as { slot: name }` spelling is refused with that
form.

```c filename=unfold_names_its_pieces_on_the_left.c
void remember(int32* p) { }
```

```click
verifying "unfold_names_its_pieces_on_the_left.c";
resource cell(p: int32*) { field revision: int32; }
resource revision_record(p: int32*, target: cell(p)) {
    field revision: int32;
    owns target;
    fact target.revision == revision;
}
void remember(int32* p) {
    owns target: cell(p);
    ensures target.revision == old(target.revision);
} by {
    let record = fold(revision_record(p, target), { revision: target.revision }, { target: target });
    unfold(record) as { target: target };
    execute();
    simp();
}
```

```expect
fail: `unfold` takes no `as` map; name the opened pieces on the left: `let { slot: name } = unfold(resource);`
```
