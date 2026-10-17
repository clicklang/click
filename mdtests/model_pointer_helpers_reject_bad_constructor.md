# A model constructor in an opaque helper must check pointer class
```c filename=forged.c
struct model_node { uint64 word; };
struct other_node { uint64 word; };
void forged(struct other_node* p) {}
```
```click
verifying "forged.c";
spec enum NodeRef { At(struct model_node*), }
function fabricated(p: struct other_node*) -> NodeRef { NodeRef::At(p) }
resource token() { field model: NodeRef; }
void forged(struct other_node* p) { produces held: token(); ensures true; } by {
 execute(); let held = fold(token(), {model: fabricated(p)});
}
```
```expect
fail: original object class
```
