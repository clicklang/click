# a call returns a nested model built over a model function

`graft` produces a `tree` whose model nests a constructor inside a
constructor, with a model-function application as the innermost field:

```
Shape::Node(Shape::Node(shape_left(old(t.model)), Shape::Empty), Shape::Empty)
```

`regraft` calls it, and the call publishes the returned instance's arm facts
under that model. A model-function application has no identity key, so the
caller must decline to index the nested constructor rather than mistake it for
a known fact. Inside `graft`, the `Shape::Node` arm also derives
`left != Shape::Empty` for the match binder `left`, which has no known
constructor, from the requirement on `shape_left(t.model)` and the equation
that unfolds it. This is the small form of the model guarantee a rotation
callback over a modeled tree carries across its rotation, and it catches a
fact key that rejects or misreads a constructor field it cannot key, or a
constructor-inequality check that gives up on a binder with no recorded
constructor instead of falling back to the stated facts.

```c filename=call_returns_a_nested_model_over_a_model_function.c
void graft(int32 *p) { }
void regraft(int32 *p) { graft(p); }
```

```click
verifying "call_returns_a_nested_model_over_a_model_function.c";

spec enum Shape {
    Empty,
    Node(Shape, Shape),
}

function shape_left(tree: Shape) -> Shape {
    match tree {
        Shape::Empty => Shape::Empty,
        Shape::Node(left, right) => left,
    }
}

resource tree(p: int32*) {
    field model: Shape;
    match model {
        Shape::Empty => { owns p[0..1]; },
        Shape::Node(left, right) => { owns p[0..1]; },
    }
}

void graft(int32* p) {
    consumes t: tree(p);
    requires t.model != Shape::Empty;
    requires shape_left(t.model) != Shape::Empty;
    produces g: tree(p);
    ensures g.model
        == Shape::Node(Shape::Node(shape_left(old(t.model)), Shape::Empty), Shape::Empty);
} by {
    match t.model {
        Shape::Empty => { contradiction(t.model == Shape::Empty); },
        Shape::Node(left, right) => {
            have shape_left(old(t.model)) == left by {
                rewrite(old(t.model) == Shape::Node(left, right));
                unfold(shape_left(Shape::Node(left, right)));
                normalize();
            }
            have left != Shape::Empty;
            unfold(t);
            let g = fold(tree(p), {
                model: Shape::Node(Shape::Node(shape_left(old(t.model)), Shape::Empty), Shape::Empty)
            });
            execute();
            simp();
        },
    }
}

void regraft(int32* p) {
    consumes t: tree(p);
    requires t.model != Shape::Empty;
    requires shape_left(t.model) != Shape::Empty;
    produces g: tree(p);
} by {
    let g = step(graft(p), { t: t });
    execute();
    simp();
}
```

```expect
pass
```
