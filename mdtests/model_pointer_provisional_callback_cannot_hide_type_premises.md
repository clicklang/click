# A provisional callback contract cannot hide its implementation's object-type premise

```c filename=callback.c
struct model_node { uint64 word; };
void wrapped(struct model_node* p) {}
int32 accept(void (*f)(struct model_node*)) { return 0; }
int32 caller() { return accept(&wrapped); }
```

```click
verifying "callback.c";
spec enum NodeRef { At(struct model_node*), }
resource token() { field model: NodeRef; }
contract void Callback(struct model_node* p) { produces held: token(); ensures true; }
int32 accept(void (*f)(struct model_node*)) {
    requires Callback(f); ensures result == 0;
} by { execute(); normalize(); }
int32 caller() { ensures result == 0; } by { execute(); }
void wrapped(struct model_node* p) { produces held: token(); ensures held.model == NodeRef::At(p); } by {
    execute(); let held = fold(token(), { model: NodeRef::At(p) });
}

```

```expect
fail: function `wrapped` does not satisfy named contract `Callback` automatically
```
