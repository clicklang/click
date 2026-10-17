# Packed pointer recovery preserves the loop object class

The input resource names the original pointer address stored in the word.
The full cast relationship retains pointer identity, while the numeric address
observation retains the source object class across the integer cast.
The loop has a reachable back edge: setting `more = 0` would miss the bug.

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
    fact ((struct node*)p->parent_word) == p;
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
            close_invariants() by simp();
        }
    }
    execute();
}
```
```expect
pass
```
