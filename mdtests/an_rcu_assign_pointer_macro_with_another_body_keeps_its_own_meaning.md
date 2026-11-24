# An `rcu_assign_pointer` macro with another body keeps its own meaning

A macro named `rcu_assign_pointer` whose body is not the recognized
definition is expanded as written. This one stores nothing, so the claim that
the slot holds the published pointer fails.

```c filename=main.c
#define rcu_assign_pointer(p, v) do { int32 rcu_unused = 0; } while (0)

struct node { int32 value; };

void publish(struct node **slot, struct node *n) {
    rcu_assign_pointer(*slot, n);
}
```

```click
verifying "main.c";

void publish(struct node **slot, struct node *n) {
    owns *slot;
    ensures *slot == n;
}
```

```expect
fail: unclosed goal
```
