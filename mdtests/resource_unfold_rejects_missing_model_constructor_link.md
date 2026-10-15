# An unconnected child model has no selected constructor

The box model does not identify its child when the intermediate model link
is missing. A constructor from another class supplies no ownership.
```c filename=probe.c
void probe(int *p) { }
```
```click
verifying "probe.c";
spec enum Model { Empty, Full(int32), }
resource inner(p: int32*) {
    field model: Model;
    match model {
        Model::Empty => { fact 1 == 1; },
        Model::Full(value) => { owns p[0..1]; fact p[0] == value; },
    }
}
resource outer(p: int32*) {
    field model: Model;
    field context: Model;
    owns child: inner(p);
    fact child.model == context;
}
void probe(int32* p) {
    owns box: outer(p);
    ensures box.model == old(box.model);
} by {
    match box.model {
        Model::Empty => {
            let { child: child } = unfold(box);
            unfold(child);
            let child = fold(inner(p), { model: Model::Empty });
            let box = fold(outer(p), { model: Model::Empty, context: Model::Empty }, { child: child });
            execute(); simp();
        },
        Model::Full(value) => {
            let { child: child } = unfold(box);
            unfold(child);
            let child = fold(inner(p), { model: Model::Full(value) });
            let box = fold(outer(p), { model: Model::Full(value), context: Model::Full(value) }, { child: child });
            execute(); simp();
        },
    }
}
```
```expect
fail: matched field `model` has no known constructor
```
