# A call must bound its write effect while a view is live

The call can name the recursive input resource, but its summary provides no
byte range for that resource's write effect. A separation goal between two
byte ranges would misdiagnose the refusal.

```c filename=unbounded_write.c
struct node { struct node *next; };
void touch(struct node *p) {}
void caller(struct node *p, int *viewed) { touch(p); }
```

```click
verifying "unbounded_write.c";

resource list(p: struct node*) {
    if p != 0 {
        owns p->next;
        owns list(p->next);
    }
}

void touch(struct node* p) { owns list(p); }
void caller(struct node* p, int* viewed) {
    requires p != 0;
    owns list(p);
    views viewed[0..1];
} by {
    step();
}
```

```expect
fail: call to `touch` has no checked byte bound for a write effect through `list(p)` while the view `viewed[0]` is live
```
