# Metadata refolding through a model-bound parent pointer

A field address displaced from a producer-retained raw pointer read must use
that read definition, just as a named read does. The parent and child come
from model constructors, so they need not share a C parameter address base.

```c filename=metadata-symbolic.c
struct node { uint64 tag; struct node *left; struct node *right; };
struct sized_node { struct node rb; int32 size; };
void metadata() { return; }
```

```click
verifying "metadata-symbolic.c";
spec enum Shape { One(struct node*, int32) }
resource size_metadata(node: struct node*) {
    field value: int32;
    owns ((struct sized_node*)(void*)node)->size;
    fact ((struct sized_node*)(void*)node)->size == value;
}
resource tree(node: struct node*) {
    field model: Shape;
    match model {
        Shape::One(child, value) => {
            owns node->left;
            owns metadata: size_metadata(node->left);
            fact node->left == child;
            fact metadata.value == value;
        },
    }
}
spec enum Outer { Root(struct node*, Shape) }
resource outer() {
    field model: Outer;
    match model {
        Outer::Root(base, shape) => {
            owns inner: tree(base);
            fact inner.model == shape;
        },
    }
}
void metadata() {
    owns o: outer();
    ensures true;
} by {
    match o.model {
        Outer::Root(base, shape) => {
            let { inner: t } = unfold(o);
            match t.model {
                Shape::One(leaf, value) => {
                    let { metadata: m } = unfold(t);
                    unfold(m);
                    let m = fold(size_metadata(leaf), { value: value });
                    let t = fold(tree(base), { model: Shape::One(leaf, value) }, { metadata: m });
                    let o = fold(outer(), { model: Outer::Root(base, Shape::One(leaf, value)) }, { inner: t });
                    execute(); normalize();
                },
            }
        },
    }
}
```

```expect
pass
```
