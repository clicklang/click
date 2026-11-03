# A call subregion retains its resource bound when its result initializes a local

```c filename=footprint.c
struct node { struct node *next; };
int touch(struct node *child) { return 0; }
void caller(struct node *child, int *slot) { int rest = touch(child); }
```

```click
verifying "footprint.c";
resource list(p: struct node*) {
    if p != 0 {
        owns p->next;
        owns list(p->next);
    }
}
int32 touch(struct node* child) { owns list(child); }
void caller(struct node* child, int32* slot) {
    owns list(child);
    owns *slot;
} by {
    step();
    step();
    have contains(list(child), statement(0).region(1).footprint) by { assumption(); }
}
```

```expect
pass
```
