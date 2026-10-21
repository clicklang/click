# A caller keeps viewed memory across a resource-taking call

```c filename=views.c
struct node { int value; struct node *next; };
void touch(struct node *node) {
}
void touch_tagged(struct node *node) {}
int keep_tagged(int *cell) {
    int value = *cell;
    touch_tagged(0);
    return value;
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
    ensures result == *cell;
} by {
    fold(list_at(0));
    execute();
    simp();
}
resource tagged_node_at(p: struct node*) {
    field tag: int32;
    if p != 0 {
        owns *p;
    }
}

void touch_tagged(struct node* node) {
    owns list: tagged_node_at(node);
} by { execute(); simp(); }

int32 keep_tagged(int32* cell) {
    views *cell;
    owns list: tagged_node_at(0);
    ensures result == *cell;
} by { execute(); simp(); }

```

```expect
pass
```
