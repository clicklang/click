# Atomic evidence rebuilds and retains ambient contexts

## Violated invariant

One proof leaf should cost and cite the premises it actually needs, rather
than unrelated ambient facts. `PureFactContext::with_only_proposition_facts`
in `src/kernel/assumptions.rs` clones the persistent context, replaces its
proposition facts, but retains every condition fact. Clearing proposition
facts rebuilds a stated-fact index over those conditions, and
`recompute_content_fingerprint` walks them again. The smart planner in
`src/surface/planning/proposition_search.rs` can construct this context for
each candidate and candidate pair. `RetainedPremises::from_context` in
`src/kernel/primitives.rs` then copies all its condition facts into the
certificate. The final atomic fallback can retain the full ambient context.

The restriction and retained-premise mechanisms are sound boundaries: the
kernel checks only cited premises. The defect is making the cited set and
work depend on facts the derivation did not need. Do not replace them with an
unchecked claim that the ambient context proves the goal.

## Intended regression

Prove a fixed atomic memory or resource goal from one or two named premises.
At multiple sizes, add unrelated condition facts and unrelated proposition
facts. Measure planner construction, certificate premise count and size,
kernel recheck, and expansion/re-verification. Include a case that reaches
the full-context fallback, so a fix to only the preferred candidate route
does not leave oversized evidence behind. Include a negative case omitting
one required premise.

## Acceptance criteria

- Candidate trials and the retained leaf do work proportional to selected
  premises and indexes actually queried, up to indexing factors, rather than
  rebuilding or copying unrelated ambient facts per trial.
- Checked evidence explicitly identifies every fact needed by the atomic
  rule, including equality, framing, and snapshot dependencies. The kernel
  validates that evidence against the available context without repeating
  smart search; deleting any required premise invalidates the derivation.
- Certificate size, checking work, and expansion work remain bounded as
  unrelated facts grow in the multi-size regression. Existing positive and
  negative proof behavior is preserved, and `scripts/check.sh` passes.
- This work can be deferred while e-graph migration proceeds, unless a
  concrete slice depends on building one of these restricted contexts.
