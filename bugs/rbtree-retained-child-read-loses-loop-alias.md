# Retained caller field cannot be transported through a loop pointer alias

Soundness: sound-but-incomplete. A checked transport of an unchanged pointer
field is refused. No false claim has been accepted. The reduction is a proof
prefix, not a completed verification of its enclosing function.

## Reproduction

On upstream `ddedb8d22` (the same verifier sources as `9d3f003e4`), run:

```sh
CLICK_NO_VERSION_DISPATCH=1 target/debug/click verify --trace-proof probe \
  bugs/repros/rbtree-retained-child-read.click
```

Use the normal `CLICK_CPP_EXPORTER` setting if required by the checkout.
The companion C keeps the insertion pattern: load the parent and transferred
child, update the parent and child's links, call a parent-word setter, then
assign the loop's node variable. It is a reduction of the unchanged Linux
insertion program, not a proposed change to that program.

The refusal takes about one second in a debug build. All earlier written
links, including `have n == old(n) by { assumption(); }`, check. The refused
simple link is:

```click
have n->right == at(before_call,n->right) by {
    transport(at(before_call,n->right) == at(before_call,n->right),
              n->right == at(before_call,n->right)) using {
        n == old(n);
    };
}
```

Output:

```text
`transport using` found no frame evidence carrying its source fact to the target's state
checked source (holds): value#1 = value#1 is true
checked target (wanted): value#2 == value#1 is true
goal: value#2 == value#1 is true
```

The relevant legend definitions are:

```text
value#1 = pointer read at snapshot#2, address value#3
value#2 = pointer read at snapshot#4, address value#4
value#3 = n + 8 bytes
value#4 = old(n) + 8 bytes
snapshot#2 = loop effect: may write [...], based on snapshot#8
snapshot#3 = recorded at statement(8).entry; call effect: may write
  [memory(value#14[Int32:0..1], stride=8)]; caller frame retained
  [...; owns memory(n[Int32:2..4], stride=4) x 1;
        owns memory(n[Int32:4..6], stride=4) x 1; ...],
  placement premises [], based on snapshot#6
snapshot#4 = project memory for pointer read(value#4), based on snapshot#3
snapshot#6 = recorded at statement(7).entry; store value#10 at
  address value#6, based on snapshot#10
value#6 = n + 16 bytes
snapshot#8 = recorded at function.entry; seed 4 Int32 cells at
  value#17, stride 4 bytes, reads from snapshot#12, holes [(0, 2)],
  based on snapshot#11
value#17 = old(n)
snapshot#12 = initial empty memory
```

The companion source also opens and re-folds `state` before the loop. Those
two lines are essential: delete both, keeping the C, loop invariant, call,
and transport unchanged, and the transport checks. The next refusal then
occurs at the deliberately unfinished `execute()` suffix. This control is
not a claim that the whole function verifies. A straight-line reduction with
ordinary field ownership also verifies the read transport and its function.

The original rbtree proof also transports `p->rb_left` successfully across
the same setter call. Both fields are eight-byte `struct rb_node*` values;
`p->rb_left` is at byte offset 16, `node->rb_right` at offset 8. The failing
query additionally crosses from a literal caller-frame base to a saved
pointer spelling. Explicitly proving and listing that pointer identity does
not repair the refusal. Root-cache validity is not needed in this reduction.

## Missing connection

The one-line argument is: the call retains the eight bytes at `n + 8`,
`n == old(n)`, hence the read at `old(n) + 8` has the same value as before
the call. The source is reflexive and needs no premise. This is covered by
**Transport with selected premises / Accepts** in
`docs/reference/tactics/index.md`: every read cell is unchanged, with its
read kind and all eight bytes preserved.

Outcome under the tracing procedure: **failing-tactic**. The checker does not
connect the retained interval to the aliased target read after the initial
unfold/fold has seeded entry memory. The trace establishes that failure and
its dependence on those proof steps; it does not establish which internal
index or memory-projection implementation is responsible. Investigate that
boundary before choosing a fix; do not add a broad alias scan or rewrite C.

## Acceptance criteria

- The retained-field transport in the companion prefix checks with the
  initial unfold/fold present, without additional proof bookkeeping.
- The same link still checks with those two steps absent.
- Preserve whole-cell coverage and scope: an actual write to the selected
  field, or an equality unavailable on the current branch, must not frame it.
- The original rbtree insertion prefix gets past this read transport without
  changing its C or requiring a valid size cache before recomputation.
