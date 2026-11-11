# A consumed resource instance is named at a mark

After a call consumes a resource instance, the current state no longer holds
it. `at(mark, name)` names the instance as it was held at that mark, so a
separation stated there can be written and selected after the call.

```c filename=named.c
struct node { struct node *next; };
void touch(struct node *child) {}
void caller(struct node *child, int *slot) { touch(child); }
```

```click
import click::separation;
verifying "named.c";
resource box(p: struct node*) {
    field tag: int32;
    owns p->next;
}
void touch(struct node* child) {
    consumes b: box(child);
    produces c: box(child);
} by {
    unfold(b);
    let c = fold(box(child), { tag: 0 });
}
void caller(struct node* child, int32* slot) {
    consumes b: box(child);
    owns *slot;
    produces c: box(child);
} by {
    have separate(b, memory(*slot)) by { assumption(); }
    mark before_call;
    let { c: c } = step(touch, { b: b });
    have separate(at(before_call, b), memory(*slot)) by { assumption(); }
    apply(separation::separate_symm(at(before_call, b), memory(*slot))) using {
        separate(at(before_call, b), memory(*slot));
    };
}
```

```expect
pass
```
