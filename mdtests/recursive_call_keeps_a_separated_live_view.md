# A recursive call keeps a separated live view

The call is bounded by the owned list. A read after the call still sees the
entry value of the viewed cell, which is separate from the entire list.

```c filename=recursive_write.c
struct node { struct node *next; };
void touch(struct node *p) {}
int caller(struct node *p, const int *slot) { touch(p); return *slot; }
```

```click
import click::separation;
verifying "recursive_write.c";

resource list(p: struct node*) {
    if p != 0 {
        owns p->next;
        owns list(p->next);
    }
}

void touch(struct node* p) { owns list(p); }
int32 caller(struct node* p, const int32* slot) {
    requires p != 0;
    owns list(p);
    views *slot;
    requires separate(list(p), memory(*slot));
    ensures result == old(*slot);
} by {
    step() {
        requires separate(list(p), memory(*slot)) by close();
    }
    step();
}
```

```expect
pass
```
