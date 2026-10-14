# Pointer disequality survives normalized same-base comparisons

Checked aliases connect a pure model pointer to a C pointer. The negative
comparison remains available when the goal uses byte offsets.

```click
spec enum Model { Empty, Node(int32*) }
function model_pointer(model: Model) -> int32* {
    match model { Model::Empty => 0, Model::Node(p) => p, }
}
theorem pointer_disequality(model: Model, p: int32*, other: int32*) {
    requires model_pointer(model) == p;
    requires model_pointer(model) != other;
    ensures p != other by {
        have model_pointer(model) == p by assumption();
        have model_pointer(model) != other by assumption();
        assumption();
    }
}
```

```expect
pass
```
