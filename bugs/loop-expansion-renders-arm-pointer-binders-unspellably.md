# Expanding a `loop` renders a match arm's pointer binder as `…`

## Violated invariant

A smart tactic that verifies expands to explicit source that verifies the
same claim (`click audit`, `AGENTS.md` "Tooling stability comes first").

A `loop` with an implicit `initialize` is a smart site. Its expansion
rewrites the whole loop, including the written `preserve` body, and an
`apply(theorem(x))` in that body whose argument `x` is a pointer bound by a
proof `match` arm (for example `identity` in
`Context::Left(identity, grandparent, ...)`) is printed as
`apply(theorem(…))`. That text does not parse, and the expansion fails with
`the expansion needs a name for a value the kernel introduced, which has no
surface spelling`. The source names the value; the printer does not use the
name.

## Reproduction

Start from `mdtests/rb_ascending_walk_to_root.md` and make three edits:

1. Add `theorem ptr_self(p: struct rb_node*) { ensures p == p by { simp(); } }`
   before `function plug`.
2. Delete the loop's `initialize by simp;`, so the loop is a smart site.
3. In the `Context::Left` arm of `preserve`, after `have identity == parent`,
   add:

   ```click
   have identity == identity by {
       apply(ptr_self(identity));
       assumption();
   }
   ```

`click verify` passes the result (2 selected proofs). `click audit` fails at
the `loop` site with the message above. Without edit 3 the audit passes all
5 sites, and with `initialize by simp;` restored it passes too, because the
loop is then not a smart site.

Printing the unparseable lines showed what the expander emitted, here and in
`examples/rbtree-insert`:

```
apply(plug_left_frame(…, …, ccolor, csib, cup, t.model)) using {
apply(rb_root_black_black_node(…, gparent, unl, unr)) using {
```

The arguments are `ContractExpression`s printed by
`format_theorem_application` in `src/surface/printing.rs`. By the time the
loop's expansion prints them, an arm-bound pointer has become a kernel value
with no source form. Where that substitution happens has not been traced.

`examples/rbtree-insert` writes `initialize by simp;` for this reason; its
loop body has dozens of such `apply`s.

## Intended regression

The reproduction above as a retained expansion-audit case that the gate
checks: expanding the `loop` site emits `apply(ptr_self(identity))`, and the
rewrite verifies.

## Acceptance criteria

- `click audit` passes on the reproduction with the loop's `initialize`
  omitted.
- The fix is in the expander or printer, not in the fixture; `scripts/check.sh`
  passes.
