# A pure getter must satisfy its declared result's object class

```c filename=getter.c
struct model_node { uint64 word; };
struct other_node { uint64 word; };
void wrong(struct other_node* p) {}
```

```click
verifying "getter.c";
spec enum NodeRef { At(struct model_node*), }
function retyped(p: struct other_node*) -> struct model_node* { p }
resource token() { field model: NodeRef; }
void wrong(struct other_node* p) {
    produces held: token();
    ensures true;
} by {
    execute();
    let held = fold(token(), { model: NodeRef::At(retyped(p)) });
}
```

```expect
fail: function `retyped` return value requires original object class `struct model_node` or null
```
