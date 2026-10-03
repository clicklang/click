# An outer lvalue that loads memory stays rejected beside an assignment

A load could read the assigned variable through an alias, so only lvalues built from direct reads of other named locals are accepted.

```c filename=c_chained_assignment_lvalue_load_rejected.c
struct node {
    unsigned long color;
    struct node *next;
};

int32 run(struct node *p, struct node *q) {
    unsigned long pc;
    p->next->color = pc = q->color;
    return 0;
}
```

```click
verifying "c_chained_assignment_lvalue_load_rejected.c";

```

```expect
fail:c_chained_assignment_lvalue_load_rejected.c:8: an assignment expression and an unsequenced operand read are not supported
```
