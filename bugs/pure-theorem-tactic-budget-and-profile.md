# Pure theorem tactics bypass per-tactic attribution and budget scopes

## Violated invariant

A written theorem proof is verifier work, and its tactics must obey the same
per-class deterministic limits and produce the same claim/tactic events as C
proofs. `click profile` must distinguish proof checking from environment setup.

Reproduced on master `2a29eb3ee3e797552cc0ae91b8bbd07f91a39a20`:

- A theorem with one `normalize()` verifies, but its profile reports zero claims
  and zero completed simple tactics. The proof is counted as environment work.
- A signed arithmetic theorem is accepted by `verify_click_theorems` with all
  three tactic-class limits set to one unit. Its collected event stream contains
  no `TacticStarted`. A C proof under those same limits is refused at `step`
  after two units and emits a tactic event. The theorem's whole-run measured
  work is 1,539 units on a warm run; that includes setup, so it is not an
  attribution of all 1,539 units to the arithmetic tactic.
- A short uint64 theorem with 32 additions verifies in about 3.9 seconds, but
  `profile` attributes 3.87 seconds to `ENVIRONMENT` and zero time to `SMART`.
  The 64-addition variant exceeded 30 seconds in ordinary verification. A
  subsequent `profile --time-limit 20s` stops at the wall-clock containment
  boundary and calls the interrupted phase `environment`, while the attached
  proof diagnostic identifies `arithmetic()` at tactic 0.

The uint64 observations demonstrate why this is more than missing counters.
They do not establish the expensive check's root cause or asymptotic complexity.
The whole-run work limit still applies. Tiny class limits may also cause numeric
lowering to refuse; that is distinct from entering a budget scope for each tactic.

## Reproduction

Save this as `/tmp/theorem-profile.click`:

```click
theorem identity(x: int32) {
    ensures x == x by { normalize(); }
}
```

Run ordinary verification first, then profile the verified theorem:

```sh
click verify /tmp/theorem-profile.click
click profile /tmp/theorem-profile.click
```

The profile currently says `0 claims`, `SIMPLE COMPLETED 0`, and no theorem or
claim rows. This happens on the trivial proof, without any expensive arithmetic.

A direct library reproduction for the budget gap:

```rust
use click::instrumentation::{collect, with_tactic_work_limits, TacticWorkLimits};
use click::surface::verify_click_theorems;

let source = r#"
    theorem bound(x: int32) {
        requires x <= 100;
        ensures x <= 1000 by {
            arithmetic() using { x <= 100; }
        }
    }
"#;
let (result, events) = collect(|| {
    with_tactic_work_limits(
        TacticWorkLimits { simple: 1, smart: 1, control: 1 },
        || verify_click_theorems(source),
    )
});
// Currently result is Ok and events contains no TacticStarted.
```

To reproduce the misleading slow-proof attribution, generate a flat expression
rather than exceeding the separate parenthesis-nesting limit:

```sh
python3 - <<'PY'
from pathlib import Path
for n in [8, 16, 32, 64]:
    expression = 'x' + ' + 1u64' * n
    Path(f'/tmp/wide-{n}.click').write_text(
        'theorem bound(x: uint64) { requires x <= 100u64; '
        f'ensures {expression} <= 1000u64 by '
        '{ arithmetic() using { x <= 100u64; } } }\n')
PY
click verify /tmp/wide-32.click
click profile /tmp/wide-32.click
click profile --time-limit 20s /tmp/wide-64.click
```

The 64-term profile is an incomplete timeout diagnostic, not a basis for
expansion. After containment, confirm that its verifier process tree exited.

## Intended regression and acceptance criteria

- Collect events for the trivial verified theorem and assert one identified
  theorem claim and one simple `normalize` step, with a source location.
- Check a nontrivial theorem under a small per-tactic budget and require a
  bounded refusal naming its tactic and claim, rather than silently accepting
  a proof whose steps were never given a budget scope.
- Exercise multiple ensures clauses, nested `have`, induction, theorem
  dependencies, and generic theorem instantiations. Shared dependency/setup
  work must remain separate; nested tactic time must not be double counted.
- Grow the uint64 sum over multiple sizes in a nightly regression. Attribute
  its actual proof work before deciding whether it needs a separate complexity
  fix. Do not increase default budgets or relabel proof work as setup.
- Keep ordinary verification, profile, expansion, audit, and library entry
  points on the same bounded proof driver. Preserve checked certificates and
  expected false-proof refusals.
