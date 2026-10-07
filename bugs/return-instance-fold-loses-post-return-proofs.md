# Return-instance certification loses proved post-return facts

Reproduced 2026-10-07 on `codex/rbtree-root-erase`, after the checked loop
semantics, returned `open` fold, and constructor-premise fixes.

## Violated invariant

A resource fold accepted by the checked proof object must remain certifiable
on the same returned execution path when its body facts were proved by a
preceding `have`. Certification must retain the checked derivations, without
accepting an arbitrary or sibling path's assumption context.

The reproduction below proves an unconditional pure function fact after
return, folds a named resource using it, then fails at the final `simp`:

```
could not certify return instance fold
return fold body is not justified on this execution path
```

## Small intended regression

Save the following as an mdtest and run `click verify` on it. It currently
fails despite the stated expected pass. Keep the proof after `execute()`;
moving it before execution hides the missing post-return evidence path.

```c filename=return_derived_fold.c
int f(int *p) { return 0; }
```
```click
verifying "return_derived_fold.c";
function reflexive(p: int32*) -> int32 { if p == p { 1 } else { 0 } }
resource Cell(p: int32*) {
    field tag: int32;
    owns p[0..1];
    fact reflexive(p) == 1;
}
int32 f(int32* p) {
    consumes p[0..1];
    produces out: Cell(p);
    ensures result == 0;
} by {
    execute();
    have reflexive(p) == 1 by { unfold(reflexive(p)); normalize(); }
    let out = fold(Cell(p), { tag: 1 });
    simp();
}
```
```expect
pass
```

## Investigation and acceptance criteria

`ProofScope::join_inner` retains a completed `have` as a fact in the outcome
proof. `record_return_resource_rewrite_with_children` checks the fold against
those facts. Later `trace_completion` rechecks the fold against
`executed_under`, retained from the returning statement; it does not include
the later proved fact. The function body remains opaque there.

Retain kernel-issued proposition completions for the particular returned
outcome and consume their checked conclusions when certifying subsequent
folds. Bind each completion to its actual path, returned state, and authorized
root assumptions. Do not replace `executed_under` with `rewrite.before_facts`:
existing tests deliberately reject folds justified only by a sibling's guard,
constructor case, or body fact. Do not scan the whole ambient context for
every `have` or fold; use shared provenance and checked deltas.

- The reproduction verifies and every smart site expands and re-verifies.
- A false body fact, a fact proved only in a sibling branch, and a fact about
  a different returned snapshot remain rejected.
- Repeated post-return proofs/folds with unrelated ambient facts have
  deterministic near-linear work, and existing return-instance path-isolation
  tests keep passing.
- Resume the unchanged C immediate-successor proof in `rbtree-example`:
  after returning, it reparents/folds the left subtree, proves
  `rb_parent_is(Node(left, successor, ...), successor) == 1`, then folds the
  successor and root. That fold currently triggers the same failure. The C
  input must remain unchanged. The published root zero/one-child proof is
  unaffected.
