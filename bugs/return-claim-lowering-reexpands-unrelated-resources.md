# Return claim lowering repeatedly expands unrelated resources

Soundness: not soundness. This is repeated deterministic work while checking
true explicit return claims. No false acceptance or incorrect refusal was
observed.

## Violated invariant

A simple return closer for `result == x` must not expand every unrelated
resource in the contract. With R unrelated folded resources and C explicit
return claims, the measured lowering work is C * (14 + 11R), although the
source, proof and necessary output are O(R + C).

## Reproduction

Generate a matrix of standalone mdtests with this script, then run each with
`click profile --top 50 --time-limit 20s PATH`. All twelve verify successfully.
The relevant nested operation is `return claim goal lowering`; its work count
isolates the repeated lowering from entry checking and final certification.

````python
from pathlib import Path

out = Path("work/return-claim-reconstruction")
out.mkdir(parents=True, exist_ok=True)
for resources in [0, 4, 16, 64]:
    for claims in [1, 4, 16]:
        holdings = "".join(f"owns marker({i});\n" for i in range(resources))
        ensures = "ensures result == x;\n" * claims
        closers = "assumption();\n" * claims
        source = f'''# Return claim reconstruction

```c filename=echo.c
int32 echo(int32 x) {{ return x; }}
```

```click
resource marker(n: int32) {{ fact n == n; }}
verifying "echo.c";
int32 echo(int32 x) {{
{holdings}{ensures}
}} by {{ step(); {closers} }}
```

```expect
pass
```
'''
        (out / f"resources-{resources}-claims-{claims}.md").write_text(source)
````

Release measurements on commit `79edd6f0735b6507a781bdb2b0c3608e6acd8d86`
(the fix from PR #1184, not the earlier duplicate-lowering baseline):

| Unrelated resources | 1 claim | 4 claims | 16 claims |
| --- | ---: | ---: | ---: |
| 0 | 14 | 56 | 224 |
| 4 | 58 | 232 | 928 |
| 16 | 190 | 760 | 3,040 |
| 64 | 718 | 2,872 | 11,488 |

Columns contain total deterministic work in `return claim goal lowering`.
The operation count equals the claim count: this survives removal of the
identical folded/unfolded lowering from PR #1184. Elapsed times of these small
fixtures are not meaningful speedup estimates.

At investigation head `14d830db5e43d582f6f696ef0f779892b9f8f688`, the complete
bodies of `c_function_ensure_goals`,
`expand_all_composite_resource_facts_at_state`,
`expand_all_composite_resource_facts_with_composites`, and
`expand_checked_authority_controls` are textually identical to the measured
revision. The investigation did not rebuild that newer revision.

## Cause and constraints

`kernel_claim_goal_forms` in `src/surface/proof/claim_proofs.rs` invokes
`c_function_ensure_goals` separately for each claim. That API reconstructs the
entry state, expands all entry composites, reconstructs the exit view, and
expands all return composites before lowering the selected ensure. None of
the marker resources is relevant to `result == x`.

Prepared entry/exit views could be shared across claims at one unchanged proof
frontier, or goal lowering could expose only resources the goal actually
needs. A prepared-view solution must not reuse views across changes to the
assumptions, checked outcome, resource representation, or function/argument
bindings. Predicate guards and authority-backed resources can depend on those
inputs. Prefer explicit ownership and lifetime of prepared views over a deep
structural cache key or revalidation pass. Closer branches may transition
outcome resources before lowering; prepare from the resulting frontier.

This investigation does not establish a safe cross-tactic invalidation scheme
or claim that all lowering time is resource reconstruction. Prior vector
release profiling attributed about 171 ms of a 2.095 s run to the entire
lowering operation, so that is an upper bound for removing it in that sample,
not a promised end-to-end improvement.

## Acceptance criteria

- Add deterministic scaling coverage with independently varied resources and
  claims. Retain the original C and explicit `assumption()` proof shape.
- Return claim lowering must not perform R resource expansions per claim for
  this resource-independent scalar goal; bound the total by approximately
  O(R + C), allowing indexing factors.
- Preserve folded and unfolded predicate goals, resource-dependent loads,
  `old(...)`, guarded composites, and changed outcome/fact/resource frontiers.
- Preserve existing proof claims, C, and budgets. Run regular scaling tests,
  the relevant C corpus, and a focused successful expansion audit.
- Report matched release measurements before claiming a practical speedup.
