# A frozen pointer relationship preserves a recursive call result

A modular pop returns a recursive resource indexed by a complete pointer read.
The earlier push supplies its relationship to `tail`; later calls must keep
that relationship available when matching the returned resource.

```c filename=chain.c
struct node { int32 value; struct node *next; };
void push(struct node *node, struct node *tail) { node->next = tail; }
void pop(struct node *node) { }
int32 roundtrip(struct node *node, struct node *tail) {
    push(node, tail);
    pop(node);
    return 0;
}
```

```click
verifying "chain.c";
resource chain(node: struct node*) {
    if node != 0 {
        owns *node;
        owns chain(node->next);
    }
}
void push(struct node* node, struct node* tail) {
    requires node != 0;
    consumes *node;
    consumes chain(tail);
    produces chain(node);
    ensures node->next == tail;
} by { execute(); fold(chain(node)); simp(); }
void pop(struct node* node) {
    requires node != 0;
    consumes chain(node);
    produces *node;
    produces chain(node->next);
    ensures node->next == old(node->next);
} by { unfold(chain(node)); execute(); simp(); }
int32 roundtrip(struct node* node, struct node* tail) {
    requires node != 0;
    owns *node;
    owns chain(tail);
    ensures result == 0;
} by { execute(); simp(); }
```

```expect
pass
```
