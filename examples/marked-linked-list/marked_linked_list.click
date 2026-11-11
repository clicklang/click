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

verifying "list_empty.c";
verifying "list_prepend.c";
verifying "list_mark.c";
verifying "list_is_marked.c";
verifying "list_next.c";
verifying "list_count_live.c";
verifying "list_destroy.c";
verifying "list_pipeline.c";

struct node* list_empty() {
    produces marked_list(result);

    ensures result == 0;
    ensures aligned(result, 8);
}

struct node* list_prepend(int32 value, struct node* tail) {
    requires aligned(tail, 8);
    consumes marked_list(tail);
    produces marked_list(result);

    ensures result == tail or result != 0;
    ensures aligned(result, 8);
} by {
    step_until(statement(1));
    if node == 0 {
        step_until(function.exit);
    } else {
        step_until(function.exit);
        have aligned(tail, 8) by assumption();
        have result->word == address(tail) by normalize();
        have (result->word & 1) == 0u64 by {
            rewrite(result->word == address(tail));
            solve() using { aligned(tail, 8); };
        }
        have result->word == address(tail) + (result->word & 1) by {
            rewrite((result->word & 1) == 0u64);
            rewrite(result->word == address(tail));
            normalize();
        }
        have ((result->word & ~1) as (struct node *)) == tail by {
            rewrite(result->word == address(tail));
            normalize() using { aligned(tail, 8); };
        }
        fold(marked_list(result));
    }
}

void list_mark(struct node* node) {
    requires node != 0;
    owns marked_list(node);

    ensures (node->word & 1) != 0;
} by {
    unfold(marked_list(node));
}

int32 list_is_marked(struct node* node) {
    requires node != 0;
    views marked_list(node);

    ensures result == 0 or result == 1;
} by {
    observe(marked_list(node));
}

struct node* list_next(struct node* node) {
    requires node != 0;
    views marked_list(node);

    ensures address(result) == (node->word & ~1);
    ensures aligned(result, 8);
} by {
    observe(marked_list(node));
    step_until(function.exit);
    have address(result) == (node->word & ~1) by {
        solve() using {
            aligned(result, 8);
            node->word == address(result) + (node->word & 1);
        }
    }
}

uint32 list_count_live(struct node* node) {
    decreases marked_list(node);
    owns marked_list(node);
} by {
    if node == 0 {
        step_until(function.exit);
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

void list_destroy(struct node* node) {
    decreases marked_list(node);
    consumes marked_list(node);
} by {
    if node == 0 {
        unfold(marked_list(node));
        step_until(function.exit);
    } else {
        unfold(marked_list(node));
        step_until(function.exit);
    }
}

int32 list_pipeline(int32 first, int32 second) {
    ensures result == 0;
}
