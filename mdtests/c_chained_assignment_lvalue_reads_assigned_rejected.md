# An outer lvalue may not read the variable the chain assigns

In `p->next = p = q`, evaluating the lvalue reads `p` while the inner assignment writes it, with no sequencing between them. C leaves that undefined.

```c filename=c_chained_assignment_lvalue_reads_assigned_rejected.c
struct node {
    unsigned long color;
    struct node *next;
};

int32 run(struct node *p, struct node *q) {
    p->next = p = q;
    return 0;
}
```

```click
verifying "c_chained_assignment_lvalue_reads_assigned_rejected.c";

```

```expect
fail:c_chained_assignment_lvalue_reads_assigned_rejected.c:7: an assignment expression and an unsequenced operand read are not supported
```
