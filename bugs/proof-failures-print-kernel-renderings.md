# Proof failures still print kernel renderings of facts

## Violated invariant

A proof failure is written for the author of the sidecar. It should name
values and addresses by their source spelling and should not expose the
kernel's own notation for a fact: anonymous value labels, memory snapshot
numbers, or load variables.

Diagnostics that fall back to the kernel proposition renderer
(`src/surface/proof_diagnostics/render.rs`) still print that notation. Over
the `click verify` output of the 1,239 failing fixtures in `mdtests/`:

- 26 fixtures print an anonymous `value A` label. The renderer names a
  variable only when it is the entry value of a parameter of the function
  being verified; a loop-carried local, a call result, or an algebraic value
  has no name there.
- 48 fixtures print a lowered fact such as
  `int32 =(load A=load(snapshot#1, pointer=occupied[start]), 0) is true` or
  `memory-mutates-only(snapshot#2 -> snapshot#3, writes=...)`, where a
  surface spelling such as `occupied[start] == 0` or `at(pre, ...)` exists.
- 1 fixture prints a raw `pointer(pointer B+0)`.

These lines appear under headings such as `lowered target`, `effect facts
relating states at this frontier`, `pure facts:`, and `requirement N ...
instantiates to ...`.

## Reproduction

`mdtests/loop_binder_instance_footprint_includes_its_memory.md` fails as
expected, and its report includes:

```
  lowered target
  int32 =(load A=load(snapshot#1, pointer=occupied[start]), 0) is true
  effect facts relating states at this frontier (showing 4 of 4):
  memory-mutates-only(snapshot#2 -> snapshot#3, writes=occupied[start] (4 bytes))
  memory-effects(snapshot#4 -> snapshot#5, ranges=1)
  int32 =(value B=w.next, value C) is true
  int32 <(value C, end) is false
```

`value C` is the loop counter, `snapshot#2 -> snapshot#3` is one store the
source can name, and the target has the surface form the same report prints
two lines earlier.

## Intended regression

A CLI test that verifies a reduced form of that fixture and asserts the
report contains neither `value ` followed by a capital letter, nor
`snapshot#`, nor `load A=`, while still naming the stored cell and the loop
counter. Add a second case whose failing fact mentions a call result.

## Acceptance criteria

- A local that is in scope at the failing tactic is printed by its name.
- A fact with a surface spelling is printed in it; a memory state is named by
  a program point or `at(...)`/`old(...)`, not a snapshot number.
- A fact with no surface spelling says so once and stays bounded; it does not
  print raw kernel notation as if it were Click.
- The counts above reach zero over the failing fixtures, with no diagnostic
  growing into a repeated internal-state dump. `scripts/check.sh` passes.
