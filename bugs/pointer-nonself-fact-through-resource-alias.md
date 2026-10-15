# Pointer non-self facts are lost through a resource alias

Soundness: incomplete. Unfolding a resource establishes that its child link
is different from its address. After the resource's modeled identity names
that same address, ordinary fact lookup cannot recover the non-self fact
through the identity alias. No false acceptance is known.

Reproduce with the embedded fixture below: `click verify --trace-proof keep
bugs/pointer-nonself-fact-through-resource-alias.md`. The inner unfold records
an offset disequality and its address identity equality. The requested
`parent->child != parent` instead lowers to a pointer disequality. The graph
has an existing pointer-to-offset truth bridge, but not the converse lookup.
The same gap blocks folding the parent in the sized insertion rotation proof.

Acceptance: the fixture passes using `assumption`; missing non-self evidence
and aliases withdrawn or unavailable in another branch remain conservative.
Queries must use only the selected addresses and indexed truth, not scan the
ambient context or enumerate all pointer aliases.

```c filename=pointer_nonself.c
struct item { uint64 word; struct item* child; };
void keep(struct item* root) {}
```
```click
verifying "pointer_nonself.c";
spec enum Tree { Leaf(struct item*), Parent(struct item*, Tree) }
resource chain(p: struct item*) {
    field model: Tree;
    match model {
        Tree::Leaf(identity) => { owns p->word; fact p == identity; },
        Tree::Parent(identity, rest) => {
            owns p->child;
            owns child: chain(p->child);
            fact p == identity;
            fact p->child != p;
            fact child.model == rest;
        },
    }
}
void keep(struct item* root) {
    consumes state: chain(root);
    ensures 1 == 1;
} by {
    match state.model {
        Tree::Leaf(identity) => { unfold(state); execute(); simp(); },
        Tree::Parent(identity, rest) => {
            let { child: inner } = unfold(state);
            match inner.model {
                Tree::Leaf(parent) => { unfold(inner); execute(); simp(); },
                Tree::Parent(parent, tail) => {
                    let { child: leaf } = unfold(inner);
                    have parent->child != parent by { assumption(); }
                    execute(); simp();
                },
            }
        },
    }
}
```
```expect
pass
```
