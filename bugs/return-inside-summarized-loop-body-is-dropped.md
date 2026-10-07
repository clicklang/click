# A `return` inside a summarized loop body is dropped from the function's paths

## Violated invariant

Every path a C function can take must reach contract certification. A loop
body that executes `return` leaves the function with the returned value and
the state at the `return`; the function's `ensures` (and its resource
bookkeeping) must be checked on that path.

`src/surface/proof/execution_planning/loop_planning.rs` (around line 1315,
`advance_preservation_region`) handles a preservation path that reached the
function exit with an empty arm whose comment says "The kernel's independently
checked body execution contributes the actual function-return outcome". It
does not: when the surface drives the preservation (explicit `preserve` or the
automation the `loop` keyword owns), `forward_planning.rs:613` sets
`preservation_proven = true`, and
`crate::kernel::loops::execute_c_while_exit_paths` (`src/kernel/loops.rs`,
called from `execute_c_while_exit_paths_with_proven_phases`) is then invoked
with `preservation_environment = None`, so the kernel never executes the body
and `collect_loop_preservation_summary` never produces the `Return` final exit
path. Only `natural_loop` (goto-formed) returns are registered as
`CLoopFinalExitCandidate`s. The resulting `CVerifiedLoopRule` has only the
guard-false exit, and the function is certified on that path alone. Note also
that `symbolic_c_statement_execution_with_loop_rule` (`src/kernel/api.rs`,
about line 4280) only forms a rule when every path is `Normal` or
`VerificationDiverges`, so a `Return` path cannot be carried by a loop rule at
all; the kernel-driven preservation (`backedge_target.is_some()` case) would
refuse the loop rather than drop the path.

## Reproduction

`f(5)` returns `7` (the body returns when `i == 2`), yet `ensures result == 5`
verifies.

```markdown
```c filename=x6.c
int32 f(int32 n) {
    int32 i = 0;
    while (i < n) {
        if (i == 2) {
            return 7;
        }
        i = i + 1;
    }
    return i;
}
```

```click
verifying "x6.c";

int32 f(int32 n) {
    requires n == 5;
    ensures result == 5;
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 0;
        invariant i <= n;
    }
    step();
    simp();
}
```
```

Observed:

```text
$ click verify repro.md
1 selected proof verified
$ echo $?
0
```

`--trace-proof f` shows a single checked branch: `declare i`, `i = 0`, then
`return i` — the `return 7` path does not exist. The same C proved with
`execute(); simp();` (bounded unrolling, no loop rule) is correctly refused
with `result == 5; left side evaluated to 7`.

The explicit form reproduces identically:
`preserve by { if i == 2 { step(); step(); } else { step(); step(); step(); close_invariants(); } }`
also prints `1 selected proof verified` with exit 0.

`mdtests/return_inside_ranked_loop_body.md` passes only because its contract
states nothing about `result`; it does not detect the dropped path.

## Intended regression

Add the repro above as a negative mdtest (expect `fail`), with both the
omitted-phase form and an explicit `preserve by { if i == 2 { step(); step(); } else { ... close_invariants(); } }`
form, and a positive sibling `ensures result == 5 or result == 7` that must
pass. Add a variant where the returning path consumes a resource
(`free(p); return 0;`) under `produces p[0..1]`, which must be refused.

## Acceptance criteria

- A `return` reached inside a summarized loop body is a function-exit path of
  the enclosing execution: the postcondition and resource/produces obligations
  are checked on it, with the returned value and the state at the `return`.
- The negative regressions above fail with a diagnostic naming the `return`
  path; the positive sibling passes.
- `symbolic_c_statement_execution_with_loop_rule` either carries `Return`
  outcomes in the rule or the surface routes them into the function's own
  path set; the surface never passes `preservation_proven = true` for a region
  whose return paths it discarded.
