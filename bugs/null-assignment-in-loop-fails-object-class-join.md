# Assigning null to a classed pointer local in a loop fails the object-class join

Soundness: incomplete. Click refuses a valid program, and nothing false is
accepted. The null pointer designates no object, and the strict join only
compares classes.

A pointer local that carries an object class at the loop head, such as a
`struct node*` parameter, is refused at the back edge when the body
assigns it the null pointer:

```c filename=nullloop.c
struct node { int32 v; };
void f(struct node* p, int32 more) {
    while (more) { p = 0; more = more - 1; }
}
```
```click
verifying "nullloop.c";
void f(struct node* p, int32 more) {
    requires 0 <= more;
    ensures 1 == 1;
} by {
    loop {
        decreases more;
        invariant 0 <= more;
        initialize by simp();
        preserve by { step(); step(); close_invariants() by simp(); }
    }
    execute();
}
```

```text
loop state join changes pointer object classes; the body path does not reach the loop-head state
pointer local `p`
loop-head object class
struct node; back-edge object class
unknown (no retained object class)
```

This reproduces at `aec1aa773`. The same refusal stops
`examples/rbtree-augmented/rbtree_size_insert_color_flip.click` and its
mirrored variant at `parent = rb_parent(node)`. There, the root's packed
parent word is `0 | RB_BLACK`, so decoding it yields null.

The violated invariant is that a valid assignment preserves the loop state
join. A null pointer value has no object, so it cannot have an incompatible
class. Strict-aliasing checks have nothing to check through null.

Do not reinstate the head's class at the join or take a class from the
destination type. How the join should treat a provably null pointer, for
example as compatible with any class, is a design decision for the
maintainer.

Acceptance: the reproduction above verifies as an mdtest. Assigning a
pointer of another struct's class is still refused
(`mdtests/a_model_field_pointer_to_another_struct_fails_the_loop_join.md`).
`rbtree_size_insert_color_flip.click` gets past the join.
