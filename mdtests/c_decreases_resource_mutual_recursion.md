# a structural resource measure ranks mutual recursion

`even` and `odd` alternate down a list described by the model-free resource
`list(node)`, each ranked by `decreases list(node)`. The structural analysis
reads each member's body: a call to another member of the recursive component
must pass, for that member's own measured requirement, a direct contained
child of this function's measured instance, on a path that establishes the
arm's guard. Every member's body is checked, so every edge of the cycle moves
to a strictly contained child of the finite witness, exactly as a self-call
does.

```c filename=c_decreases_resource_mutual_recursion_even.c
struct node { int value; struct node *next; };

int even(struct node *node) {
    int result;
    if (node != 0) {
        result = odd(node->next);
        return result;
    }
    return 0;
}
```

```c filename=c_decreases_resource_mutual_recursion_odd.c
struct node { int value; struct node *next; };

int odd(struct node *node) {
    int result;
    if (node != 0) {
        result = even(node->next);
        return result;
    }
    return 0;
}
```

```click
resource list(node: struct node*) {
    if node != 0 {
        owns node->value;
        owns node->next;
        owns list(node->next);
    }
}

verifying "c_decreases_resource_mutual_recursion_even.c";
verifying "c_decreases_resource_mutual_recursion_odd.c";

int32 even(struct node* node) {
    decreases list(node);
    views list(node);
    ensures result == 0;
} by {
    if node == 0 {
        execute();
        simp();
    } else {
        observe(list(node));
        execute();
        simp();
    }
}

int32 odd(struct node* node) {
    decreases list(node);
    views list(node);
    ensures result == 0;
} by {
    if node == 0 {
        execute();
        simp();
    } else {
        observe(list(node));
        execute();
        simp();
    }
}
```

```expect
pass
```
