# A named unfold witness spells its body facts

`let { parent: p } = unfold(linked(node))` names the resource's `let ...
where` witness. The body facts the unfold publishes are spelled with that
name, `aligned(p, 8)` and `node->word == address(p) + (node->word & 1)`, so
the implicit `solve` after the fold can cite both to prove the masked
postcondition.

```c filename=a_named_unfold_witness_spells_its_body_facts.c
struct node {
    unsigned long word;
};

struct node* parent_of(struct node* node) {
    return (struct node*)(node->word & ~3);
}
```

```click
resource linked(node: struct node*) {
    owns node->word;
    let parent: struct node* where aligned(parent, 8) and
        node->word == address(parent) + (node->word & 1);
}

verifying "a_named_unfold_witness_spells_its_body_facts.c";

struct node* parent_of(struct node* node) {
    requires node != 0;
    owns linked(node);
    ensures address(result) == (node->word & ~3);
} by {
    let { parent: p } = unfold(linked(node));
    step_until(function.exit);
    fold(linked(node));
    solve();
}
```

```expect
pass
```
