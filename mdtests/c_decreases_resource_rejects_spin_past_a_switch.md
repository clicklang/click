# a structural measure rejects a recursive call that follows a switch

A `switch` with one returning case and no `default` still lets the unmatched
selector fall past it, so the resource-measure walk must keep that path alive
and check the recursive call after the switch. `spin_past_a_switch` recurses on
its own parameter, so `decreases zero_list(node)` is false and must be refused.
This catches a structural walk that answers a `switch` with only its case
bodies' paths and so walks no recursive call after it.

```c filename=c_decreases_resource_rejects_spin_past_a_switch.c
struct node {
    struct node* next;
};

int32 spin_past_a_switch(struct node* node, int32 k) {
    int32 result;
    switch (k) {
        case 0:
            return 0;
    }
    result = spin_past_a_switch(node, k);
    return result;
}
```

```click
resource zero_list(node: struct node*) {
    if node != 0 {
        owns node->next;
        owns zero_list(node->next);
    }
}

verifying "c_decreases_resource_rejects_spin_past_a_switch.c";

int32 spin_past_a_switch(struct node* node, int32 k) {
    decreases zero_list(node);
    requires node != 0;
    views zero_list(node);
} by {
    execute();
    simp();
}
```

```expect
fail: does not pass a direct contained child of its structural resource measure
```
