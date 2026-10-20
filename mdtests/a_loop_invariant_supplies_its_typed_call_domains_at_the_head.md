# A loop invariant supplies its typed call domains at the head

`is_node` takes a `struct node*`, so calling it requires evidence that the
argument's original object class is `struct node`. The loop reassigns `p`, so
at the loop head `p` is a fresh value with no evidence of its own. The
invariant `is_node(p) == 1` is checked by ordinary lowering at entry and at the
back edge, where `p` and `q` carry the contract's typed requirements, so the
head may assume the domain together with the invariant. The refusal when the
back edge cannot establish it is
[`a_loop_invariant_typed_call_domain_must_hold_at_the_back_edge.md`](a_loop_invariant_typed_call_domain_must_hold_at_the_back_edge.md).
The original is [`rb_ascending_walk_to_root.md`](rb_ascending_walk_to_root.md),
whose invariants call typed helpers on the reassigned `parent`.

```c filename=a_loop_invariant_supplies_its_typed_call_domains_at_the_head.c
struct node { int32 value; };

struct node* settle(struct node* p, struct node* q, int32 n) {
    while (n > 0) {
        p = q;
        n = n - 1;
    }
    return p;
}
```

```click
verifying "a_loop_invariant_supplies_its_typed_call_domains_at_the_head.c";

function is_node(p: struct node*) -> int32 { 1 }

struct node* settle(struct node* p, struct node* q, int32 n) {
    requires is_node(p) == 1;
    requires is_node(q) == 1;
    ensures true;
} by {
    loop {
        decreases n;
        invariant is_node(p) == 1;
        initialize by simp();
        preserve by { step(); step(); close_invariants(); }
    }
    execute();
}
```

```expect
pass
```
