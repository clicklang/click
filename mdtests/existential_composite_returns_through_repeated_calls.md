# A witnessed composite survives repeated checked calls

Each returned occurrence instantiates its witness once. Its constructed body
supplies admission and projection, including when the witness is related to
an owned word rather than exposed as a contract parameter.

```c filename=existential_return_calls.c
struct node { int32 value; unsigned long word; };
void keep(struct node* node) {}
void forward(struct node* node) { keep(node); keep(node); }
```

```click
resource packed(node: struct node*) {
    owns *node;
    let next: struct node* where aligned(next, 8) and node->word == address(next) + (node->word & 1);
}

verifying "existential_return_calls.c";
void keep(struct node* node) {
    requires node != 0;
    owns packed(node);
}
void forward(struct node* node) {
    requires node != 0;
    owns packed(node);
}
```

```expect
pass
```
