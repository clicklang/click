# A self-linked loop keeps its pointer's class across a word conversion

The sized red-black color-flip path assigns `node = gparent`, where
`gparent` comes back from the packed integer parent word and so carries no
object class. This reduction follows a self link through an integer field:
`p` is proved unchanged, yet each iteration rebuilds it from an integer. The
loop head keeps `struct node`'s class and the unclassed back edge keeps it,
since a class only adds strict-aliasing refusals.

```c filename=packed.c
struct node { uint64 parent_word; };
void follow(struct node* p, int32 more) {
    while (more) { p = (struct node*)p->parent_word; more = more - 1; }
}
```
```click
verifying "packed.c";
resource self_link(p: struct node*) {
    field word: uint64;
    owns p->parent_word;
    fact p->parent_word == word;
    fact word == address(p);
}
void follow(struct node* p, int32 more) {
    owns held: self_link(p);
    requires 0 <= more;
    ensures 1 == 1;
} by {
    loop {
        owns held: self_link(old(p));
        decreases more;
        invariant p == old(p);
        invariant 0 <= more;
        initialize by simp();
        preserve by {
            let { word: saved_word } = unfold(held);
            have p->parent_word == address(p) by { assumption(); }
            step(); step();
            let held = fold(self_link(old(p)), { word: saved_word });
            close_invariants() by { simp(); }
        }
    }
    execute();
}
```
```expect
pass
```
