# A fold at a return names its witness as `result`

`unfold(packed(node))` without a `let` leaves the witness `next` unnamed. The
function returns that pointer, so at the closing `fold` the witness is the
returned value, and the fold's open body facts are spelled with `result`:
`aligned(result, 8)` and `node->word == address(result) + (node->word & 1)`.
The `close() using` after the fold cites exactly those spellings.

```c filename=a_fold_at_a_return_names_its_witness_as_result.c
struct node {
    int32 value;
    unsigned long word;
};

struct node* unpack(struct node* node) {
    return (struct node*)(node->word & ~1);
}
```

```click
resource packed(node: struct node*) {
    owns *node;
    let next: struct node* where aligned(next, 8) and node->word == address(next) + (node->word & 1);
}

verifying "a_fold_at_a_return_names_its_witness_as_result.c";

struct node* unpack(struct node* node) {
    requires node != 0;
    owns packed(node);
    ensures address(result) == (node->word & ~1);
} by {
    unfold(packed(node));
    step_until(function.exit);
    fold(packed(node));
    close();
    close() using {
        aligned(result, 8);
        node->word == address(result) + (node->word & 1);
    };
}
```

```expect
pass
```
