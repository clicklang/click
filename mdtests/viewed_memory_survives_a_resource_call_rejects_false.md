# Framing a view does not change its value

```c filename=views.c
struct node { int value; struct node *next; };
void touch(struct node *node) {
}
int keep(int *cell) {
    int value = *cell;
    touch(0);
    return value;
}
```

```click
verifying "views.c";

resource list_at(p: struct node*) {
    if p != 0 {
        owns *p;
        owns list_at(p->next);
    }
}

void touch(struct node* node) {
    owns list_at(node);
} by {
    execute();
    simp();
}

int32 keep(int32* cell) {
    views *cell;
    ensures result == *cell + 1;
} by {
    fold(list_at(0));
    execute();
    simp();
}
```

```expect
fail: unclosed goal
```
