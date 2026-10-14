# Bare theorem application uses scoped model equality closure

The owned input models establish `x.model == y.model` and
`shape(z.model) == shape(y.model)`. The theorem application must accept
`shape(x.model) == shape(z.model)` through the same equality closure as
`assumption()`, without an extra `have` that restates that derived equality.

```c filename=model_apply.c
void use_models(void) {}
```

```click
verifying "model_apply.c";
spec enum Model { Empty, Node(int32) }
spec enum Shape { Empty, Node }
function shape(m: Model) -> Shape {
    match m { Model::Empty => Shape::Empty, Model::Node(n) => Shape::Node, }
}
resource ghost(id: int32) { field model: Model; }
theorem same_shape(a: Model, b: Model) {
    requires shape(a) == shape(b);
    ensures shape(a) == shape(b) by { assumption(); }
}
void use_models() {
    owns x: ghost(0);
    owns y: ghost(1);
    owns z: ghost(2);
    requires x.model == y.model;
    requires shape(z.model) == shape(y.model);
    ensures 0 == 0;
} by {
    apply(same_shape(x.model, z.model));
    execute(); simp();
}
```

```expect
pass
```
