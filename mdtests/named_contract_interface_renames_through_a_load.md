# a named contract's interface identity renames through a load

`probe` declares the same clauses as the named contract `Linked`, with a
different parameter name, and one clause owns a cell reached through a loaded
pointer, `owns n->next->value`. The execution theorem that `probe` satisfies
`Linked` compares the two interfaces exactly modulo parameter names, so the
renaming must reach the parameter under that load. This catches an interface
identity that skips the pointer operand of a typed load and so refuses an
identical contract.

```c filename=named_contract_interface_renames_through_a_load.c
struct node {
    struct node *next;
    int32 value;
};

void probe(struct node *n) { }
```

```click
verifying "named_contract_interface_renames_through_a_load.c";

contract void Linked(struct node* node) {
    owns node->next;
    owns node->next->value;
}

void probe(struct node* n) {
    owns n->next;
    owns n->next->value;
}

theorem probe_is_linked() executes probe(struct node* n) {
    ensures Linked(&probe) by {
        execute();
        simp();
    }
}
```

```expect
pass
```
