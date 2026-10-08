# Preserved model identity does not preserve a scalar after a write

Matching the rebuilt resource keeps the color identity. It cannot make a
pre-write low bit survive an assignment that clears the tag.

```c filename=overwrite.c
struct node { unsigned long tag; struct node *other; struct node *next; };
void probe(struct node *p) { p->tag = 0; }
```

```click
verifying "overwrite.c";
spec enum Color { Red, Black }
function color_bit(color: Color) -> int { match color { Color::Red => 0, Color::Black => 1, } }
spec enum Tag { At(struct node*, Color) }
function identity(model: Tag) -> struct node* { match model { Tag::At(id, color) => id, } }
resource child(p: struct node*) { field model: Color; owns p->tag; }
resource frame() {
    field model: Tag;
    match model {
        Tag::At(id, color) => {
            owns id->tag;
            owns id->other;
            owns kid: child(id->other);
            fact kid.model == color;
            fact (id->tag & 1) == color_bit(color);
            fact (id->tag & 1) == 1;
        },
    }
}
void probe(struct node *p) {
    consumes a: frame();
    requires p == identity(a.model);
    produces b: frame();
    ensures b.model == old(a.model);
} by {
    match a.model {
        Tag::At(id, color) => {
            have p == id by {
                rewrite(p == identity(a.model));
                rewrite(a.model == Tag::At(id, color));
                unfold(identity(Tag::At(id, color))); normalize();
            }
            let {kid: original_kid} = unfold(a);
            let joined = fold(frame(), {model: Tag::At(id, color)}, {kid: original_kid});
            match joined.model {
                Tag::At(other, other_color) => {
                    have joined.model == Tag::At(other, other_color) by { simp(); }
                    let {kid: kid} = unfold(joined);
                    step();
                    have (other->tag & 1) == 1 by { simp(); }
                    let b = fold(frame(), {model: Tag::At(id, color)}, {kid: kid});
                    execute(); simp();
                },
            }
        },
    }
}
```

```expect
fail: could not establish `(other->tag & 1) == 1`
```
