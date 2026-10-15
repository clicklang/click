# An ordinary exit produces a composite without checking its body facts

Priority: P1.

Soundness: unsound. A function whose contract produces, or returns under
`owns`, a fieldless composite whose body owns memory verifies when the proof
never folds the composite, even though a C store has made a body fact false.
The caller receives the composite and, after unfolding it, the false fact. In
the reproduction `use` verifies `ensures result == 0` while it returns `9`.

## Violated invariant

A composite instance is held only when its body holds: its memory clauses are
owned and every `fact` is true of the current memory. An explicit
`fold(zt(p))` checks this and refuses (`requires an exact body fact`); the
ordinary exit must apply the same check, or refuse the unfolded pieces in
place of the composite.

## Reproduction

```c filename=exit_produces_unchecked_composite.c
void mk(unsigned char *p)
{
	p[5] = 9;
}

unsigned char use(unsigned char *p)
{
	mk(p);
	return p[5];
}
```

```click
resource zt(p: uint8*) {
    owns p[0..6];
    fact p[5] == 0;
}

verifying "exit_produces_unchecked_composite.c";

void mk(uint8* p) {
    consumes p[0..6];
    produces zt(p);
} by {
    execute();
}

uint8 use(uint8* p) {
    owns p[0..6];
    ensures result == 0;
} by {
    step();
    unfold(zt(p));
    execute();
    simp();
}
```

Observed on `cstrimpl` at `ca5d178a` (master `67eff880` plus #1073), with
and without that branch's changes: `2 selected proofs verified`.

The same hole appears in three shapes, all verifying:

- `consumes p[0..6]; requires p[5] == 7; produces zt(p);` with a body that
  writes `p[5] = 9` and no `fold` (above, without the caller);
- `owns zt(p);` with `unfold(zt(p)); execute();` over `p[5] = 'x';` and no
  `fold` — an `owns` contract that breaks its instance and never returns it;
- `consumes zt(p); produces zt2(p);` for a second resource with the same
  body, again with no `fold`.

A field-bearing named binder (`owns z: zt(p);` with a `field`) is refused
correctly: `missing resource fact owns zt(p)`.

A debug print in `prove_ensure_resource` (`src/surface/checking.rs`) shows the
outcome snapshot it checks already holds `owns zt(p)` beside `views p[0..6]`,
although `--trace-proof` shows the unfold removed both and no fold re-added
them, and an explicit `unfold(zt(p))` after `execute()` reports "the rewritten
composite is absent from both resource representations". So the composite is
restored in the published outcome somewhere between the C return and the
claim check, without its facts; the kernel certification accepts the same
outcome. Not yet located.

This blocks the owning `cstr_at` body approved for borrowed C strings: with it,
a function declared `owns cstr_at(p, 5u64)` that writes `p[2] = 0` verifies
without refolding, so "a function that shortens must use consumes/produces"
does not hold.

## Acceptance

- The reproduction fails, naming the unestablished body fact `p[5] == 0` of
  `zt(p)` (or the missing fold) at `mk`'s exit; it is kept as an mdtest, with
  the `owns zt(p)` and `consumes zt / produces zt2` shapes.
- A positive twin verifies: `mk` writing `p[5] = 0` and producing `zt(p)`
  with an explicit `fold(zt(p))` (and, if ordinary exits keep folding
  automatically, without it).
- The kernel refuses the same certificate independently of the Surface.
