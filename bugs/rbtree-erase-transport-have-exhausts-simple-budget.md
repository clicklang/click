# A `transport` `have` in `rbtree-erase` exhausts the simple budget

The nightly example `examples/rbtree-erase` fails on master `d7501d30f`. A
simple `have ... by { transport(...) using { ...; } }` spends the whole
simple-tactic budget:

```sh
CLICK_EXAMPLE=rbtree-erase cargo test --release --test examples example_projects
```

```text
`____rb_erase_color.contract` tactic 10 (`loop`), `preserve` tactic 182:
`have` failed for `separate(memory(iid->rb_right), memory(tmp2->__rb_parent_color))`:
verification budget exhausted inside tactic `have` in `____rb_erase_color.contract`
exhausted its deterministic simple work budget after 750001 units
(750000 limit; statement 91, source tactic 799)
```

The step is in
`examples/rbtree-erase/rbtree_erase_color_flips_red_all.click` (lines 1708
and 2366). It transports one separation fact across `sibling == iid`, with
both premises named in its `using` list. The example is in `NIGHTLY` in
`tests/examples.rs`, so the gate does not run it. The breaking commit is not
yet bisected.

The broken invariant: a simple tactic does work proportional to its
explicit input, the affected operation and the proof-state delta
(`docs/internals/verification-efficiency.md`). A `transport` of one fact
across one named equality has a small explicit input, and spending 750,000
units means it is scanning or searching state it was not given.

Acceptance:
- `examples/rbtree-erase` verifies on master without raising any budget.
- A gate regression transports one `separate` fact across one named pointer
  equality beside a growing number of unrelated owned cells and facts, and
  shows the step's work constant in their number, up to logarithmic factors.
