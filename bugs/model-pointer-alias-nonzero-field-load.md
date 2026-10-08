# A model pointer alias loses equality of a nonzero-offset pointer field

## Violated invariant

Two equal addresses in the same defining snapshot must give the same pointer
load, including when one address uses a pointer introduced by a model match.
The neighboring regression `mdtests/egraph_resource_pointer_load_alias.md`
checks this for a field at offset zero. The same proof fails with a pointer
field at byte offset 16. No C statement, store, or unowned read intervenes.

Reproduced on commit `008b7a4586391252a9bde09539b10d5e3238dd21`, and with
the subsequent same-block pointer-transitivity fix. This blocks the
`close_erase_spine_link` helper for the deeper rbtree successor splice.

## Small intended regression

Save these as `probe.c` and `probe.click`, then run `click verify probe.click`.
The address equality passes. The next `have` fails with
`could not establish p->next == id->next`. Moving `next` to the first field
makes the proof verify, which is diagnostic evidence only: the fix must
verify the original layout. Explicit `rewrite(p == id)` and
`rewrite(&p->next == &id->next)` at the failing load equality also refuse:
`rewrite equality does not occur in the current goal`. This is not just a
missed `simp` search.

```c
struct node { unsigned long tag; struct node *other; struct node *next; };
void probe(struct node *p, struct node *q, struct node *value) {}
```

```click
verifying "probe.c";
spec enum Tag { At(struct node*) }
resource alias(p: struct node*) {
    field model: Tag;
    match model {
        Tag::At(id) => { fact p == id; },
    }
}
void probe(struct node *p, struct node *q, struct node *value) {
    consumes p->next;
    consumes a: alias(p);
    requires p->next == value;
    produces p->next;
    produces b: alias(p);
    ensures p->next == value;
} by {
    match a.model {
        Tag::At(id) => {
            unfold(a);
            have p == id by { simp(); }
            have &p->next == &id->next by { simp(); }
            have p->next == id->next by { simp(); }
            have id->next == value by { simp(); }
            let b = fold(alias(p), { model: Tag::At(id) });
            execute(); simp();
        },
    }
}
```

## Acceptance criteria

- The unchanged reproducer verifies and its expanded proof rechecks.
- Add coverage for nonzero field offsets and model-introduced aliases.
  Different fields, changed snapshots, and missing ownership remain distinct.
- Preserve indexed, context-local pointer-load reasoning. Do not scan ambient
  facts or memory history, add eager all-pairs bridges, or change the C layout.
- Resume the rbtree frame-closing proof after this regression is green.
