# Matching a rebuilt resource preserves its algebraic payload identity

The first match exposes the color variable. Rebuilding the resource carries
that immutable value into another match; the fresh source name must still
name the same color inside the wide scalar fact. The checked match equation
must also remain available in the written bindings.

```c filename=empty.c
struct node { unsigned long tag; struct node *other; struct node *next; };
void probe(struct node *p) {}
```

```click
verifying "empty.c";
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
            let {kid: original_kid} = unfold(a);
            let joined = fold(frame(), {model: Tag::At(id, color)}, {kid: original_kid});
            match joined.model {
                Tag::At(other, other_color) => {
                    have joined.model == Tag::At(other, other_color) by { simp(); }
                    let {kid: kid} = unfold(joined);
                    have (other->tag & 1) == color_bit(other_color) by { simp(); }
                    let b = fold(frame(), {model: Tag::At(id, color)}, {kid: kid});
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
