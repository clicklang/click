# Equal-address wide reads and pointer substitution do not compose in a fold

Reproduced on `f815994d7` (PR #624) while refolding `Context::Right` after
an outer rotation in the focused rbtree erase proof. The original C is
unchanged. The fold reaches body fact 5 after the earlier sibling-argument
failure was fixed.

## Violated invariant

Checked reads of the same type at equal addresses in the same snapshot denote
equal values. These equalities and already-established pointer equalities
should compose inside the parent/color equation being refolded. This case
needs no additional mathematical premise.

## Reproduced state

Here `read64` abbreviates a registered `Bits64` read, and `M` is one identical
snapshot, not two snapshots connected by an assumed frame. The established
context contains:

```text
p = zid
q = sid
v = read64(M, zid)
v = address(sid) + (v & 1)
```

The rejected body fact is:

```text
a = read64(M, p)
a = address(q) + (a & 1)
```

`p` and `q` are saved pointer-read representations; `zid` and `sid` are named
model pointers. In the focused proof, the successful `have` is at line 1541
and the failed fold at line 1549. No program writes occur between them.

A temporary probe after normal fold rejection inspected the exact
`established_assumptions` context. It found the accepted equation and both
pointer equalities still present. For `a` and `v`, snapshot equality and
`pointers_known_equal` both returned true, but
`required_obligation_is_exactly_discharged` and `memory_loads_proven_equal`
both failed to establish their equality.

Supplying `a = v` to a diagnostic clone did not discharge the full goal.
Substituting `a` with `v`, then applying the retained `q = sid` pointer fact
with the existing equality-rewrite routine, produced a proposition the
original context discharged. This isolates two missing compositions. The
probe's supplied read equality is a diagnostic counterfactual, not a checked
certificate or a verifier fix. No altered context was used to accept the
proof, and the temporary probe was removed.

## Relevant implementation boundaries

- `atomic_memory_load_equality_evidence` requires structurally identical
  pointer terms.
- `checked_origin_load_equality` only takes its differing-pointer-block alias
  route for four-byte reads. The 64-bit read through the named `zid` alias
  cannot use that route.
- The equality graph handles pointer reads and int32 congruence; that does
  not provide general congruence for 64-bit expressions.
- `resource_body_fact_is_established` substitutes indexed explicit uint64
  neighbors. It does not combine the read equality and the nested parent
  pointer substitution in this case.

Upstream `cda316d85` adds named-snapshot selection to the alias route but
retains its four-byte restriction; the fold fallback is unchanged. The
instrumented reproduction above was run on `f815994d7`.

## Reproduction artifacts and intended regression

The investigation workspace retains the original focused proof at
`/tmp/rbtree-red-propagation/rbtree-erase/flips-red-outer-focused.click`,
the complete probe output at
`/workspace/artifacts/rbtree-word-context-probe-final.txt`, and the removed
instrumentation at `/workspace/artifacts/rbtree-word-context-probe.patch`.
The probe output uses its own labels, distinct from the appended ordinary
trace. A plain reproduction is:

```sh
click verify --trace-proof ____rb_erase_color --trace-to 1549 \
  /tmp/rbtree-red-propagation/rbtree-erase/flips-red-outer-focused.click
```

Reduce the retained-state example above to a checked kernel regression, then
retain a source-level fold regression with saved pointer reads, model aliases,
and a packed 64-bit parent word. Recheck the original focused proof after the
fix; the retained-state notation above is not yet a standalone executable test.

## Acceptance criteria

- The two equal-address same-snapshot 64-bit reads have checked equality
  evidence available to ordinary consumers.
- That evidence composes with the existing parent-pointer equality inside the
  packed-word equation, so this body fact passes without extra proof assertions.
- Missing pointer equality, incompatible read widths, changed snapshots, and
  facts confined to another branch do not authorize the same conclusion.
- The fix belongs in shared checked equality reasoning, not an rbtree-specific
  fold exception. No numeric work-budget increase is needed.
