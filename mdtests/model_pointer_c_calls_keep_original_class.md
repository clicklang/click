# A checked C call must not manufacture a model pointer class
```c filename=call.c
struct model_node { uint64 word; };
struct other_node { uint64 word; };
void wrapped(struct model_node* p) {}
void caller(struct model_node* p) { wrapped(p); }
```
```click
verifying "call.c";
spec enum NodeRef { At(struct model_node*), }
resource token() { field model: NodeRef; }
void wrapped(struct model_node* p) { produces held: token(); ensures held.model == NodeRef::At(p); } by {
 execute(); let held = fold(token(), { model: NodeRef::At(p) });
}
void caller(struct model_node* p) { produces held: token(); ensures held.model == NodeRef::At(p); } by { let { held: held } = step(wrapped(p), {}); execute(); }
```
```expect
pass
```
