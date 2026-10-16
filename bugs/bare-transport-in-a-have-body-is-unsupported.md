# A bare `transport` in a `have` body is refused as unsupported

Soundness: incomplete. A documented proof operation is refused; nothing false
is accepted.

The tactic reference (`docs/reference/tactics/index.md`) documents the bare
`transport(P, Q)`, which selects its own frame evidence, with no restriction
on where it is written. Between a contract's top-level steps it works. Inside
a `have` body the same tactic is refused with `unsupported proof operation
`transport``, while the explicit `transport(P, Q) using { ... }` is accepted
there. The have-body runner (`run_addressed_linear_script` in
`src/surface/proof/smart_closures.rs`) handles `ProofTactic::Transport` in
its goal-closing bookkeeping but has no arm for it, and `explicit_linear_step`
maps only `TransportUsing`.

Routing the bare form through `try_execution_fact_transport` there makes the
reproduction below verify, but the premise planner that backs a miss,
`apply_planned_fact_transport`, needs the execution view, which a `have`
scope does not own: it then fails with `execution proof lost its checked
frontier`. A fix has to give the planner the enclosing frontier.

## Reproduction

```c filename=t.c
int32 keep(int32 p[3]) {
    int32 local;
    local = 0;
    return local;
}
```

```click
verifying "t.c";
int32 keep(int32 p[3]) {
    views p[0..3];
    requires p[0] == 5;
    ensures p[0] == 5;
} by {
    step();
    step();
    have p[0] == 5 by {
        transport(at(function.entry, p[0] == 5), p[0] == 5);
    }
    execute();
    simp();
}
```

Observed on 2026-10-16 on master `40d34180` plus the M3 `memcpy`/`memcmp` contract change, which does not touch this path: `unsupported proof operation
`transport``. The same `transport` written directly after the second
`step()`, outside the `have`, verifies.

Found while trying to state the bytes `label_copy` copies
(`examples/label-build-flags`, `design/borrowed-c-strings.md` step 4).

## Acceptance

- The reproduction verifies, kept as an mdtest, and its expansion prints the
  selected `transport ... using`.
- A bare `transport` in a `have` body whose evidence the planner must find
  verifies too, or is refused with the planner's own diagnostic, never with
  a lost-frontier error.
- A pure theorem's `have` keeps refusing the bare form with a clear message.
