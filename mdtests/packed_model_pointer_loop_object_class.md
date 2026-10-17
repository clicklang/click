# A model-field pointer keeps its object class across a packed loop

A spec enum field declared `struct model_node*` carries that struct's object
class, as a `struct model_node*` parameter does. The loop recovers `p` from a
packed word whose origin is the matched model field `q`; encoding `q` retains
its class, so decoding restores it and the back edge keeps the head's class.
This is the reduction of the sized rbtree color flip (`node = gparent`).

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
    match model { PackedLink::At(q) => { owns p->parent_word; fact p->parent_word == word; fact q == p; fact word == address(q); }, }
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
