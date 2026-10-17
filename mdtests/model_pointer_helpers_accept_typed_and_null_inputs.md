# Pure model constructors accept typed object pointers and null

```c filename=helper.c
struct model_node { uint64 word; };
void direct(struct model_node* p) {}
void null_input(void) {}
void known_null(void* p) {}
```

```click
verifying "helper.c";
spec enum NodeRef { At(struct model_node*), }
function wrapped(p: struct model_node*) -> NodeRef { NodeRef::At(p) }
function forwarded(p: struct model_node*) -> NodeRef { wrapped(p) }
resource token() { field model: NodeRef; }
void direct(struct model_node* p) { produces held: token(); ensures held.model == forwarded(p); } by {
    execute(); let held = fold(token(), { model: forwarded(p) });
}
void null_input() { produces held: token(); ensures true; } by {
    execute(); let held = fold(token(), { model: forwarded(0) });
}
void known_null(void* p) { requires p == 0; produces held: token(); ensures true; } by {
    execute(); let held = fold(token(), { model: forwarded((struct model_node*)p) });
}
```

```expect
pass
```
