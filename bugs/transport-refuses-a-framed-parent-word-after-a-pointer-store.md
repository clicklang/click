# Transport refuses a framed parent word after a pointer store

Soundness: incomplete. The refused goal says that a readable eight-byte parent
word is unchanged by a store to a separate child-pointer field. The proof
checks the separation and pointer identities before the transport. No false
acceptance is known.

## Reproduction

Reproduced on master `db6f4b344`. Save the
[checked prefix](reproductions/rbtree_parent_word_single_store.click) beside
the existing rbtree sidecars, so its unchanged imports resolve within their
project, then trace the selected function:

```sh
cp bugs/reproductions/rbtree_parent_word_single_store.click examples/rbtree/rbtree-augmented/rbtree_size_parent_word_frame_repro.click
click verify --trace-proof insert::__rb_insert examples/rbtree/rbtree-augmented/rbtree_size_parent_word_frame_repro.click
```

Remove that temporary example file after reproducing. It is an intentionally
failing prefix, not a new example to include in the example gate. The Linux C
and shared resources are unchanged. The prefix removes the unrelated in-order
theorem and all subsequent rotation proof steps. A flat-resource probe with
the same struct layout, volatile store, and loop verifies; the retained tree
resource and snapshot context still matter to this reproduction.

## Proved chain and refused link

The prefix proves:

- `parent == p` and `gparent == g`;
- `at(before_inner_rotation, g->rb_left) == parent`;
- `at(before_inner_rotation, g->rb_left) == old(g->rb_left)`;
- preservation of `p->rb_left` across the store;
- `separate(memory(p->__rb_parent_color), memory(parent->rb_right))`;
- separation and preservation of `g->rb_left` across that store.

The only intervening C write is `WRITE_ONCE(parent->rb_right, tmp)`. The next
link is:

```click
have p->__rb_parent_color == at(before_inner_child_store, p->__rb_parent_color) by {
    transport(at(before_inner_child_store, p->__rb_parent_color) == at(before_inner_child_store, p->__rb_parent_color),
              p->__rb_parent_color == at(before_inner_child_store, p->__rb_parent_color)) using {
        parent == p;
        separate(memory(p->__rb_parent_color), memory(parent->rb_right));
        at(before_inner_rotation, g->rb_left) == parent;
        at(before_inner_rotation, g->rb_left) == old(g->rb_left);
        gparent == g;
        g->rb_left == at(before_inner_child_store, g->rb_left);
        separate(memory(g->rb_left), memory(parent->rb_right));
    };
}
```

It refuses promptly, without exhausting a budget:

```text
`transport using` found no frame evidence carrying its source fact to the target's state
goal: bits64 =(load E=read<Bits64>(snapshot#1, pointer=value#5), load F=read<Bits64>(snapshot#2, pointer=value#5)) is true
```

The shared legend defines both projected memories and the common address.
Actual cell-walk observations say `step not proved separate from the queried
bytes`; supplemental history is explicitly separate from those observations.
This localizes the refusal but does not establish its internal cause.

## Expected behavior and acceptance criteria

Tracing outcome: `failing-tactic`. The **Accepts** section of
`click docs transport` promises structural framing read by read, including
64-bit equality, across steps whose writes leave the read cells unchanged.
Mathematically, the checked eight-byte read range and write range are disjoint,
so the load is unchanged.

Make this selected transport verify with its ordinary budget and no additional
proof-only bookkeeping. Retain the projected-memory, alias, and volatile-store
pattern in a regression; the smaller flat-resource probe already passes.
Also check that a store to the parent word itself still invalidates the old
value. Do not change the Linux C or raise the work allowance.
