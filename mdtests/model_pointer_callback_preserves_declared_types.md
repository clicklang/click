# Callback formation shares the type requirements of its declared contract

```c filename=callback_types.c
struct model_node { uint64 word; };
void wrapped(struct model_node* p) {}
int32 accept(void (*f)(struct model_node*)) { return 0; }
int32 caller() { return accept(&wrapped); }
```

```click
verifying "callback_types.c";
spec enum Ref { At(struct model_node*), }
resource token() { field model: Ref; }
contract void Callback(struct model_node* p) {
    produces held: token();
    ensures held.model == Ref::At(p);
}
void wrapped(struct model_node* p) {
    produces held: token();
    ensures held.model == Ref::At(p);
} by {
    execute(); let held = fold(token(), { model: Ref::At(p) });
}
theorem wrapped_is_callback() executes wrapped(struct model_node* p) {
    ensures Callback(&wrapped) as { held: r } by {
        let { held: r } = step(wrapped(p), {});
        simp();
    }
}
int32 accept(void (*f)(struct model_node*)) {
    requires Callback(f); ensures result == 0;
} by { execute(); normalize(); }
int32 caller() { ensures result == 0; } by { apply(wrapped_is_callback()); execute(); }
```

```expect
pass
```
