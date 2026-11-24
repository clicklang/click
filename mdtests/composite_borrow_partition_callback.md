# Callback preservation through a composite-owned write

```c filename=callback.c
struct node { int value; };
struct callbacks { void (*invoke)(void); };
void update(struct node *p, const struct callbacks *cb) {
    p->value = 1;
    cb->invoke();
}
```
```click
verifying "callback.c";
contract void Callback() { ensures 1 == 1; }
resource node_cell(p: struct node*) { owns p->value; }
resource callback_table(cb: const struct callbacks*) {
    views cb->invoke;
    fact Callback(cb->invoke);
}
void update(struct node* p, const struct callbacks* cb) {
    owns node_cell(p);
    views callback_table(cb);
    ensures p->value == 1;
} by {
    unfold(node_cell(p));
    with(callback_table(cb)) {
        have separate(memory(cb->invoke), memory(p->value));
        mark before;
        step();
        have separate(statement(0).footprint, memory(cb->invoke)) by {
            close() using { separate(memory(cb->invoke), memory(p->value)); };
        }
        have cb->invoke == at(before, cb->invoke) by {
            preserve(memory(cb->invoke), statement(0));
        }
        step_until(function.exit);
    }
    fold(node_cell(p));
    close();
}
```
```expect
pass
```
