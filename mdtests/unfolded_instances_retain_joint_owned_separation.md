# Separation after instance unfolds

Fields exposed by two independent instance unfolds still belong to one ownership partition. A selected separation must use that live partition without enumerating unrelated pairs.

```c filename=unfolded_instances_retain_joint_owned_separation.c
struct node { uint64 tag; };
void user(struct node *p, struct node *q) {}
```

```click
verifying "unfolded_instances_retain_joint_owned_separation.c";
resource owned(p: struct node*) { field model: int32; owns p->tag; }
resource borrowed(p: struct node*) { field model: int32; views p->tag; }
void user(struct node* p, struct node* q) {
    consumes a: owned(p);
    consumes b: owned(q);
    produces p->tag;
    produces q->tag;
    ensures separate(memory(p->tag), memory(q->tag));
} by {
    unfold(a); unfold(b);
    have separate(memory(p->tag), memory(q->tag)) by { assumption(); }
    execute(); simp();
}
```

```expect
pass
```
