# Guarded resource facts survive a disjoint store

```c filename=guarded.c
struct base { struct base* left; struct base* right; uint64 padding; };
struct cell { struct base base; int32 value; };
int32 f(struct cell* root) {
    struct base* child = root->base.left;
    int32 value = ((struct cell*)(void*)child)->value;
    struct cell *selected = (struct cell*)(void*)child;
    selected->value = 0;
    root->value = value;
    return value;
}
```

```click
verifying "guarded.c";
resource child_value(p: struct base*) {
    field number: int32;
    if p != 0 {
        owns (p as (void *) as (struct cell *))->value;
        fact (p as (void *) as (struct cell *))->value == number;
    }
}
int32 f(struct cell* root) {
    requires root != 0;
    views root->base.left;
    owns child: child_value(root->base.left);
    owns root->value;
    requires root->base.left != 0;
    requires root->base.left != root as (void *) as (struct base *);
    requires child.number != 0;
    ensures result == old(child.number);
    ensures child.number == old(child.number);
    ensures root->value == old(child.number);
} by { unfold(child); step_until(function.exit); fold(child); solve(); }
```

```expect
fail: fold requires the instance body facts
```
