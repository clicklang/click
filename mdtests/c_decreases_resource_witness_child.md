# structural descent through a resource witness child

A `let` witness of a recursive resource has no C spelling, so a recursive
call cannot name it syntactically. The structural measure accepts the call
when the exact definition, instantiated over a symbolic entry state, lets the
pure kernel decide that the call's argument is the witness pointer: here the
where-fact and the alignment evidence make `(node->word & ~1) as (struct node *)`
the witness. The ordinary contract still certifies the resource transfer.

```c filename=c_decreases_resource_witness_child.c
struct node {
    int32 value;
    unsigned long word;
};

uint32 count_nodes(struct node *node) {
    if (node == 0) {
        return 0;
    }
    uint32 rest = count_nodes((struct node *)(node->word & ~1));
    return rest + 1;
}
```

```click
import click::separation;
resource marked_list(node: struct node*) {
    if node != 0 {
        owns allocation(node, sizeof(struct node));
        owns *node;
        fact aligned(node, 8);
        let next: struct node* where aligned(next, 8) and node->word == address(next) + (node->word & 1) and ((node->word & ~1) as (struct node *)) == next;
        owns marked_list(next);
    }
}

verifying "c_decreases_resource_witness_child.c";

uint32 count_nodes(struct node* node) {
    decreases marked_list(node);
    owns marked_list(node);
} by {
    if node == 0 {
        step_until(function.exit);
        solve();
    } else {
        let { next: child } = unfold(marked_list(node));
        step_until(statement(1));
        mark before_local;
        step();
        have separate(statement(1).region(0).footprint, memory(node->word)) by {
            normalize() using {};
        }
        have *((&node->word) as (int32 **)) == at(before_local, *((&node->word) as (int32 **))) by {
            transport_certificate {
                premise 0: separate(statement(1).region(0).footprint, memory(node->word))
                    => separate(statement(1).region(0).footprint, memory(node->word));
                preserve 0 => *((&node->word) as (int32 **)) == at(before_local, *((&node->word) as (int32 **)));
                conclusion 1;
            }
        }
        have ((node->word & ~1) as (struct node *)) == child by { assumption(); }
        have separate(marked_list(child), memory(node->word)) by { assumption(); }
        mark before_call;
        step();
        have contains(marked_list(child), statement(1).region(1).footprint) by { assumption(); }
        apply(separation::contains_refl(memory(node->word))) using {};
        apply(separation::restrict(marked_list(child), memory(node->word), statement(1).region(1).footprint, memory(node->word))) using {
            separate(marked_list(child), memory(node->word));
            contains(marked_list(child), statement(1).region(1).footprint);
            contains(memory(node->word), memory(node->word));
        };
        have *((&node->word) as (int32 **)) == at(before_call, *((&node->word) as (int32 **))) by {
            transport_certificate {
                premise 0: separate(statement(1).region(1).footprint, memory(node->word))
                    => separate(statement(1).region(1).footprint, memory(node->word));
                preserve 0 => *((&node->word) as (int32 **)) == at(before_call, *((&node->word) as (int32 **)));
                conclusion 1;
            }
        }
        have ((node->word & ~1) as (struct node *)) == child by { assumption(); }

    }
}
```

```expect
pass
```
