# A loop back edge refuses a struct pointer that returns unclassed

Soundness: incomplete. A valid loop is refused; nothing false is accepted.
The object class a pointer carries only adds strict-aliasing refusals, and an
unclassed pointer is not checked, so a loop head that keeps the class refuses
at least everything the unclassed pointer would.

Since `215e2c358` ("Check struct access paths for strict aliasing"), a
struct-pointer parameter designates its struct. A loop keeps a pointer
local's class across the abstract iteration
(`havoc_loop_modified_locals`), and the back edge
(`c_loop_state_components_match_at_back_edge_inner` in
`src/kernel/loops.rs`) refuses any local whose class differs from the head's,
including one that comes back with no class. Linux's `____rb_erase_color`
walks up with `node = parent; parent = rb_parent(node);`, and `rb_parent`
converts the parent-and-color word to a pointer, which carries no class. The
head's `parent` designates `struct rb_node` and the back edge returns it
unclassed, so the join is refused:

```sh
cargo build --release --bin click
CLICK_DISABLE_TACTIC_BUDGETS=1 target/release/click verify \
  examples/rbtree-erase/rbtree_erase_color_flips_red_all.click
```

```text
proof error:
  loop state join
  loop state join changes pointer object classes; the body path does not reach the loop-head state
tactic@1553:
  close_invariants();
```

A diagnostic print at the check names `parent`: head `struct rb_node`, back
edge unclassed (`root` keeps `struct rb_root`). First bad commit, by
first-parent bisection over master from `d86757df2` (good) to `f2f23e727`:
merge `88694184d`, whose only commit is `215e2c358`.

Small reproduction, with the original pattern (a struct-pointer parameter
reassigned in the loop from a tag-masked word):

```c
struct node { unsigned long parent_color; struct node *left; };
#define node_parent(pc) ((struct node *)((pc) & ~3UL))
int climb(struct node *parent, void *up, int a) {
    struct node *node = 0;
    unsigned long pc = (unsigned long)up;
    while (a != 0) {
        node = parent;
        parent = node_parent(pc);
        a = a - 1;
    }
    return a;
}
```

Acceptance: a back edge that returns a classed pointer local unclassed keeps
the head's class and is accepted
(`mdtests/a_loop_may_return_a_struct_pointer_unclassed_from_its_tag_bits.md`);
one that returns it designating another class is still refused
(`mdtests/a_loop_returning_a_pointer_to_another_struct_is_refused.md`); and
the rbtree sidecar again stops only at the loop control budget
(`bugs/rbtree-erase-flips-red-all-loop-exceeds-control-budget.md`).
