# Model pointer fields keep their declared object class

Matching the model recovers the original object class needed by the packed
pointer round trip and its reachable loop back edge. The numeric address
relation alone does not promise the stored pointer's designation and bounds;
the resource also states the complete pointer round trip.

```c filename=packed_model.c
struct model_node { uint64 parent_word; };
void follow_model(struct model_node* p, int32 more) {
    while (more) { p = (struct model_node*)p->parent_word; more = more - 1; }
}
```
```click
verifying "packed_model.c";
spec enum PackedLink { At(struct model_node*), }
resource model_link(p: struct model_node*) {
    field word: uint64;
    field model: PackedLink;
    match model { PackedLink::At(q) => { owns p->parent_word; fact p->parent_word == word; fact q == p; fact word == address(q); fact ((struct model_node*)p->parent_word) == q; }, }
}
void follow_model(struct model_node* p, int32 more) {
    owns held: model_link(p);
    requires 0 <= more;
    ensures 1 == 1;
} by {
    loop {
        owns held: model_link(old(p));
        decreases more;
        invariant p == old(p);
        invariant 0 <= more;
        initialize by simp();
        preserve by {
            match held.model { PackedLink::At(q) => {
            let { word: saved_word } = unfold(held);
            have p->parent_word == address(q) by { assumption(); }
            step(); step();
            let held = fold(model_link(old(p)), { word: saved_word, model: PackedLink::At(q) });
            close_invariants() by simp();
            } }
        }
    }
    execute();
}
```
```expect
pass
```
