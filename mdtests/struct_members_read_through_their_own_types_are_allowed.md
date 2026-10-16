# Struct members read through their own types are allowed

The strict-aliasing check allows each of these accesses:

- a member access through the object's own struct type after a `void *`
  round trip;
- an `int *` read of a struct whose member is an `int` (GCC's alias sets
  agree);
- a read through a pointer to a declared local's member;
- a member access through a struct pointer loaded from a member of that
  type.

```c filename=structs.c
struct a { int x; };
struct node { struct node *next; int v; };

int own(struct a *pa) {
    void *v = pa;
    struct a *q = v;
    return q->x;
}

int member_int(struct a *pa) {
    void *v = pa;
    int *ip = v;
    return *ip;
}

int local_own(void) {
    struct a s;
    s.x = 1;
    int *ip = &s.x;
    return *ip;
}

int loaded_own(struct node *n) {
    struct node *m = n->next;
    return m->v;
}
```

```click
verifying "structs.c";

int32 own(struct a *pa) {
    views pa->x;
    ensures true;
} by {
    execute();
}

int32 member_int(struct a *pa) {
    views pa->x;
    ensures true;
} by {
    execute();
}

int32 local_own() {
    ensures result == 1;
} by {
    execute();
    simp();
}

int32 loaded_own(struct node *n) {
    views n->next;
    views n->next->v;
    ensures true;
} by {
    execute();
}
```

```expect
pass
```
