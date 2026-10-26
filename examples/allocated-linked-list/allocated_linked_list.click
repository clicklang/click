resource allocated_list(node: struct node*) {
    if node != 0 {
        owns allocation(node, sizeof(struct node));
        owns *node;
        owns allocated_list(node->next);
    }
}

verifying "list_empty.c";
verifying "list_prepend.c";
verifying "list_head.c";
verifying "list_drop_front.c";
verifying "list_destroy.c";
verifying "list_pipeline.c";

struct node* list_empty() {
    produces allocated_list(result);

    ensures result == 0;
}

struct node* list_prepend(int32 value, struct node* tail) {
    consumes allocated_list(tail);
    produces allocated_list(result);

    ensures result == tail or result != 0;
    ensures result != tail implies result->value == value;
    ensures result != tail implies result->next == tail;
} by {
    step_until(statement(1));
    if node == 0 {
        step_until(function.exit);
    } else {
        step_until(function.exit);
        fold(allocated_list(result));
    }
}

int32 list_head(struct node* node) {
    requires node != 0;
    views allocated_list(node);

    ensures result == node->value;
} by {
    observe(allocated_list(node));
}

struct node* list_drop_front(struct node* node) {
    requires node != 0;
    consumes allocated_list(node);
    produces allocated_list(result);

    ensures result == old(node->next);
} by {
    unfold(allocated_list(node));
}

void list_destroy(struct node* node) {
    decreases allocated_list(node);
    consumes allocated_list(node);
} by {
    if node == 0 {
        unfold(allocated_list(node));
        step_until(function.exit);
    } else {
        unfold(allocated_list(node));
        step_until(function.exit);
    }
}

int32 list_pipeline(int32 first, int32 second) {
    ensures result == 0;
}
