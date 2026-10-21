# A branch interface supplies its typed call domains at the join

`is_node` takes a `struct node*`, so calling it requires evidence that the
argument's original object class is `struct node`. Both arms assign `r`, so
at the join `r` is a fresh value with no evidence of its own. Each arm checks
`is_node(r) == 1` with ordinary lowering, where `r` is `p` or `q` and carries
the contract's typed requirement, so the join may assume the domain together
with the fact. The refusal when an arm cannot establish it is
[`a_branch_interface_typed_call_domain_must_hold_in_each_arm.md`](a_branch_interface_typed_call_domain_must_hold_in_each_arm.md).
The original is `examples/rbtree/rbtree-erase/rbtree_erase_color_flips_red_all.click`,
whose `match ... ensuring` facts call `rb_reparent(irm, parent)`.

```c filename=a_branch_interface_supplies_its_typed_call_domains_at_the_join.c
struct node { int32 value; };

struct node* pick(struct node* p, struct node* q, int32 c) {
    struct node* r;
    if (c > 0) {
        r = p;
    } else {
        r = q;
    }
    return r;
}
```

```click
verifying "a_branch_interface_supplies_its_typed_call_domains_at_the_join.c";

function is_node(p: struct node*) -> int32 { 1 }

struct node* pick(struct node* p, struct node* q, int32 c) {
    requires is_node(p) == 1;
    requires is_node(q) == 1;
    ensures is_node(result) == 1;
} by {
    step();
    branch ensuring {
        fact is_node(r) == 1;
    } then {
        step();
    } else {
        step();
    }
    step();
    simp();
}
```

```expect
pass
```
