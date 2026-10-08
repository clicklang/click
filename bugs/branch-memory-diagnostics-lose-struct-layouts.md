# Branch memory diagnostics lose the source struct layout

## Violated invariant

A diagnostic about a source field must name that field, or explicitly name
byte coordinates when its source layout is unavailable. `node[2]` on a
`struct rb_node*` means the third struct, not the pointer field eight bytes
into the first struct.

The source-aware memory-range printer now recovers field names and correct
source element units, but branch-condition failures build naming tables from
kernel state alone. Those tables lose the source struct layout and still
print kernel cells as struct indices.

## Reproduction

```sh
click verify mdtests/rb_next_conjunctive_guard.md
```

The unchanged C reads `node->rb_right` while `rb_at(node)` remains folded. The
proof correctly refuses the read, but reports:

```text
the read requires `views node[2]`, which is not available
```

This was reproduced after the source-aware range-printer fix. The fixture's
current expected failure retains this spelling; change it to the field name
when this bug is fixed. Keep the C and the permission refusal unchanged.

## Cause

`proof_condition_runtime_error` in
`src/surface/proof/execution_planning/transition_certification.rs` calls
`diagnostics::local_naming_tables(state)`. It creates fresh C0 parameters from
kernel local values without the parsed C0 struct metadata, then calls
`describe_resource_fact`. The compatible kernel pointer type alone cannot
identify the source pointee struct.

Preserve source type/layout metadata when naming current state locals. Use
the current local pointer values, not stale function-entry argument values:
a parameter or local can have been reassigned before the failing branch.

## Intended regression and acceptance

- The existing fixture still fails for the missing read permission, but says
  `views node->rb_right`.
- Cover a struct pointer parameter and a reassigned or aliased struct pointer
  local; the diagnostic names the field through the current local.
- When source layout is unavailable, use explicitly identified byte units
  instead of a purported source struct index.
- The relevant `scripts/check.sh` gate passes.
