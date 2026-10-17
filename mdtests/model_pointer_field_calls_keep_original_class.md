# A typed field must not turn an unrelated object pointer into a model node
```c filename=field.c
struct node { uint64 word; };
struct other { uint64 word; };
struct holder { struct node* child; };
void wrapped(struct node* p) {}
void caller(struct holder* h, struct other* p) {
    h->child = (struct node*)(void*)p;
    wrapped(h->child);
}
```
```click
verifying "field.c";
spec enum Ref { At(struct node*), }
resource token() { field model: Ref; }
void wrapped(struct node* p) { produces held: token(); ensures held.model == Ref::At(p); } by {
    execute(); let held = fold(token(), { model: Ref::At(p) });
}
void caller(struct holder* h, struct other* p) {
    owns h->child;
    produces held: token();
    ensures true;
} by {
    step();
    let { held: held } = step(wrapped(h->child), {});
    execute();
}
```
```expect
fail: passes an object of type `struct other`
```
