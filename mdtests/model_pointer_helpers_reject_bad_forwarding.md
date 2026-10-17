# Pure helper forwarding checks the actual original object class

```c filename=helper.c
struct model_node { uint64 word; };
struct other_node { uint64 word; };
void unused(void) {}
```

```click
verifying "helper.c";
spec enum NodeRef { At(struct model_node*), }
function wrapped(p: struct model_node*) -> NodeRef { NodeRef::At(p) }
function wrong(p: struct other_node*) -> NodeRef { wrapped(p) }
```

```expect
fail: call `wrapped` parameter `p` requires original object class `struct model_node` or null
```
