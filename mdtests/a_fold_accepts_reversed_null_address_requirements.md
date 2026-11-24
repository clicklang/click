# a fold matches a null-address requirement in either operand order

```c filename=stop.c
struct node { int value; };
void stop(void) {}
```

```click
verifying "stop.c";
spec enum Tree { Node(struct node*) }
spec enum Context { Top }
function context_parent(context: Context, stop: struct node*) -> struct node* {
    match context { Context::Top => stop, }
}
resource stopped() {
    field model: Tree;
    field context: Context;
    match model { Tree::Node(parent) => {
        fact parent == context_parent(context, 0);
    }, }
}
void stop() {
    produces state: stopped();
    ensures state.model == Tree::Node(0);
    ensures state.context == Context::Top;
} by {
    have 0 == context_parent(Context::Top, 0) by {
        unfold(context_parent(Context::Top, 0)); close();
    }
    let state = fold(stopped(), { model: Tree::Node(0), context: Context::Top });
}
```

```expect
pass
```
