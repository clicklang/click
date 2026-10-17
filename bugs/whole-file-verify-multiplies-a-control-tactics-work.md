# Whole-file `verify` multiplies one control tactic's work over a selected-unit run

Soundness: not soundness. A proof is refused for exhausting its
deterministic budget; nothing false is accepted.

The same proof unit in the same file costs a control tactic about 375,000
work units when `click verify FILE:LINE:COLUMN` selects it, and exhausts the
2,500,000-unit control budget when `click verify FILE` checks the whole file.
A tactic's deterministic work should depend on its proof unit, not on which
other units the command checks: whole-file and selected-unit verification
disagree, and an edit that `verify FILE:LINE:COLUMN` accepts breaks
`verify FILE`.

## Reproduction

In `examples/arena/arena_cells.click`, inside `arena_pipeline`'s
`have forall (k: int32) { 0 <= k and k < arena->capacity implies
arena->occupied[k] == 0 } by { ... }` (the second `have` with that statement
in the file), replace

```click
            have at(f4, combined->arena->occupied[k]) == at(f4, arena->occupied[k]) by {
                simp() using {
                    at(f4, combined->arena) == arena;
                };
            }
```

with

```click
            have at(f4, combined->arena->occupied[k]) == at(f4, arena->occupied[k]) by auto();
```

Then, with `LINE` the line of the enclosing `have forall` (4862 on master at
filing):

```sh
cargo build --release --bin click
CLICK_TIMINGS=1 target/release/click verify examples/arena/arena_cells.click:LINE:5
CLICK_TIMINGS=1 target/release/click verify examples/arena/arena_cells.click
```

```text
selected unit:  tactic arena_pipeline.contract 308 have class control statement 35 source 347 0.23s work 375495
                1 selected proof verified
whole file:     tactic arena_pipeline.contract 308 have class control statement 35 source 347 2.35s work 2500001
                verification budget exhausted inside tactic `have` in `arena_pipeline.contract`
                exhausted its deterministic control work budget after 2500001 units
```

Both runs are deterministic. Unedited, the file verifies both ways, and its
tactics' work agrees between the two modes within about 15%; the selected-unit
run is usually the larger. The same replacement of the same `have`
statement in the block's other branch (75 lines further on) reproduces it
too; replacing any of six other `have`s of that block does not.

## Intended regression

A gate test that checks this unit both ways, with the edit above applied to a
copy of the sidecar, and asserts that the control tactic's work in the
whole-file run is within a small factor of its work in the selected-unit
run, and that both runs verify.

## Acceptance criteria

- With the edit applied, `click verify examples/arena/arena_cells.click`
  verifies, and the `have` at statement 35, source tactic 347, spends work
  comparable to the selected-unit run.
- The cause is named: which state carried over from the other units the
  whole-file run checks (a cache, an interning table, a recorded fact set)
  makes this tactic's structural work grow, and the fix keeps a tactic's
  work independent of the other units checked.
- The regression above is in the gate.
