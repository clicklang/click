# A claim with no kernel goal is proved as a surface lowering and then refused by certification

Soundness: incomplete. A proof the proof checker accepts is refused later by
certification. Nothing false is accepted: the refusal is the conservative
side. The defect is that two parts of the verifier can disagree about one
proof, and that the fallback is a produce-then-check path.

Invariant: a proof step is valid by construction, and the kernel does not
re-derive what the same session produced
(`docs/internals/verification-efficiency.md#construction-not-re-validation`).
A proof that checks is not refused afterwards.

## What happens

To close a contract claim the surface asks the kernel for its own goal for
that claim (`kernel_claim_goal` in `src/surface/proof/driver/claims.rs`,
which calls `CFunctionEnsureGoalContext::goals`). When the kernel returns
one, the proof closes that goal and its completion is tagged with the claim
(`PropositionObligation::for_claim_goal`, `src/kernel/proof/obligations.rs`);
certification accepts it by identity.

When the kernel returns no goal, `focus_claim_goal` falls back to
`focus_fixed_state_surface_goal`: the surface lowers the claim itself and
proves that proposition. The completion carries no claim. Certification
(`function_claim_holds_on_prepared_path`,
`src/kernel/api/contract_certification/contract_claims.rs`) then finds no
completion for the claim, tries to re-derive it, and can fail with:

```text
could not certify contract for `f`: exact symbolic execution did not establish
every contract claim; unverified claims: f.ensures_0 `...`
proof trace unavailable: no checked path was retained for this failure
```

after every tactic of the proof has checked.

## Reproduction

No reproduction on unmodified master is known. It was observed while
investigating clicklang/click#2630, with this change to
`initial_call_state` (`src/surface/lowering/resource_lowering.rs`), which
skips declaring a by-value struct parameter's input object:

```rust
    if std::env::var_os("BVNOIMAGE").is_none()
        && parameters.iter().any(|parameter| parameter.is_struct_value())
    {
```

and

```c filename=r.c
struct packet { uint32 n; };
void change(uint32* n) { *n = 9; }
uint32 consume(struct packet p) { uint32 before = p.n; change(&p.n); return before; }
```

```click
verifying "r.c";
void change(uint32* n) { owns n[0..1]; ensures *n == 9u32; }
uint32 consume(struct packet p) { ensures result == old(p.n); }
```

With `BVNOIMAGE=1`, `consume` passes its proof and is refused by
certification as above. A probe showed the proof handed certification one
checked proposition for `consume` and none tagged with
`EnsureProposition(0)`. That `kernel_claim_goal` returned `None` there is
inferred from this, not observed directly.

A first task is to find a master reproduction: any claim for which
`CFunctionEnsureGoalContext::goals` returns `None` or more than one goal
while the surface lowering succeeds.

## Acceptance criteria

- A claim for which the kernel yields no goal is refused where the proof
  opens it, with a message naming the claim and why it has no goal; the
  surface does not prove its own lowering in its place.
- No proof whose tactics all check is later refused by certification. A
  regression pins the reproduction found above.
- Certification no longer re-derives a proposition claim the proof closed.
