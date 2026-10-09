# An aliased child pointer cannot be refolded after a framed call

## Reproduction

On `62305fa67`, save the Markdown fixture below and run `click verify` on it.
The call owns only `q->tag`; the caller keeps the parent pointer field and
its folded child. The verifier refuses the final parent fold with:

```text
selected child does not satisfy the proposed parent model
```

The same C and proof pass when the parent resource spells its two owned
clauses with `p->other` instead of `id->other`. Removing the call and its
`step()` also passes. `p == id` is a checked resource-body fact; the two
spellings must denote the same field. The child model matches; the child
pointer argument is the failed comparison.

This was reduced from the non-root rbtree successor splice. It is independent
of the already-fixed ABI field width and caller-kept range lookup defects.

# A folded child survives a call to a separately owned field

```c filename=probe.c
struct node { unsigned long tag; struct node *other; struct node *next; };
void helper(struct node *q) { q->tag = 0; }
void probe(struct node *p, struct node *q) { helper(q); }
```

```click
verifying "probe.c";
spec enum Tag { At(struct node*, Child) }
spec enum Child { Empty }
resource child(p: struct node*) { field model: Child; owns p->tag; }
resource frame(p: struct node*) {
    field model: Tag;
    match model {
        Tag::At(id, cm) => {
            owns id->other;
            owns kid: child(id->other);
            fact kid.model == cm;
            fact p == id;
        },
    }
}
void helper(struct node *q) { owns q->tag; } by { execute(); simp(); }
void probe(struct node *p, struct node *q) {
    owns q->tag;
    consumes a: frame(p);
    produces b: frame(p);
    ensures b.model == old(a.model);
} by {
    match a.model {
        Tag::At(id, cm) => {
            let {kid: kid} = unfold(a);
            have p == id by { assumption(); }
            step();
            let b = fold(frame(p), {model: Tag::At(id, cm)}, {kid: kid});
            execute(); simp();
        },
    }
}
```

```expect
pass
```

## Investigation

The original child argument and the proposed fold argument retain typed
8-byte read definitions with different storage-base spellings. Their read
addresses are proven equal, but the resource argument equality does not
connect their values. A single unrelated store passes; one modular call
suffices to expose the failure. Explicit equality of the current reads and
of the child's model does not discharge the fold.

Do not fix this by comparing only pointer offsets or a 32-bit fragment.
Both block identity and the complete pointer value matter. Temporary
experiments following only a canonical projection or normalizing the
immediate materialization base did not resolve the reproduction.

## Acceptance

- The fixture verifies with its C and aliased resource clauses unchanged.
- Expansion audit agrees with verification.
- Replacing the pointer field after the call rejects a stale child fold.
- A partial pointer overwrite and a missing/withdrawn base alias cannot
  establish preservation.
- Pointer equality and provenance lookup have deterministic scaling
  coverage over unrelated fields and facts; no history or environment scans
  are added to each logical read.
