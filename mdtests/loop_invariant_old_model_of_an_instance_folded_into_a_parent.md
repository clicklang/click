# `old(c.model)` in a loop invariant after `c` was folded into another instance

`count_down` consumes `c` and hands back a wrapper that owns it. The proof
folds the wrapper before the loop, and the loop's invariant relates the
wrapper's model to the model `c` had at function entry.

`old(c.model)` is refused there. A loop clause reads `old(name.field)` through
the instance of that name the loop's entry state holds, and after the fold
there is none: `c` is a child of `w`. The refusal names the fold that consumed
`c` and suggests keeping the model payload through a match on the held
wrapper. The neighbouring [positive](loop_invariant_binds_model_from_a_folded_parent.md)
uses that binding in the loop invariant. An unfold pattern binds only C-typed
fields, so it cannot bind this algebraic model.

A descent that pushes its entry context under a new frame has exactly this
shape. The unchanged Linux `rb_next` folds `ctx_at(node->rb_right)` over the
entry context and then walks left, and the walk's invariant has to relate the
frames it pushed to the context the function was given
([`rb_next.md`](rb_next.md)). That proof names the entry context by matching
the frame it has just folded, whose last field is that context. The fixture
pins the refusal for the direct spelling; it becomes a positive when a loop
clause can read a function-entry model whose instance the loop does not hold,
or when a proof can name a model value directly.

```c filename=count_down.c
struct node { int32 shade; };

int32 count_down(struct node* p, int32 n) {
    while (n > 0)
        n = n - 1;
    return 0;
}
```

```click
verifying "count_down.c";

spec enum Cell {
    Missing,
    Present(struct node*),
}

spec enum Wrap { Wrap(Cell) }

resource cell_at(p: struct node*) {
    field model: Cell;
    match model {
        Cell::Missing => { fact p == 0; },
        Cell::Present(identity) => {
            owns identity->shade;
            fact p != 0;
            fact p == identity;
        },
    }
}

resource wrap_at(p: struct node*) {
    field model: Wrap;
    match model {
        Wrap::Wrap(inner_model) => {
            owns inner: cell_at(p);
            fact inner.model == inner_model;
        },
    }
}

int32 count_down(struct node* p, int32 n) {
    requires n >= 0;
    consumes c: cell_at(p);
    produces w: wrap_at(p);
    ensures w.model == Wrap::Wrap(old(c.model));
} by {
    let w = fold(wrap_at(p), { model: Wrap::Wrap(old(c.model)) }, { inner: c });
    loop {
        decreases n;
        owns w: wrap_at(p);
        invariant n >= 0;
        invariant w.model == Wrap::Wrap(old(c.model));
    }
    execute();
    simp();
}
```

```expect
fail: it was consumed as child `inner` when `w` was folded. Where the held parent's model carries the child's model, match it before the loop
```
