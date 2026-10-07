# A contract exit returns a folded composite and its body children as separate resources

## Violated invariant

Owned resources are linear. A function returns exactly the resources its
contract names at exit, and a folded composite holds its body once, inside
itself (`docs/concepts/resources.md`, "Owned memory", "Composite resources";
`docs/internals/separation-logic.md`, "Resource state"). A function holding
only `wrap(p)` (whose body is `owns p[0..1]`) must not satisfy both
`owns wrap(p)` and `produces p[0..1]`: that hands the caller the cell twice,
once directly and once inside the composite. Click accepts it with an empty
C body and `by auto`, and the dual (`owns p[0..1]; produces wrap(p);`) and
a two-child form (`owns wrap2(p); produces p[0..1]; produces p[1..2];`)
verify the same way. The duplicated ownership lets a caller prove a false
postcondition through the "two owners are two places" rule.

Responsible code. Each returned resource clause (`owns`, `produces`,
borrowed returns) is a separate contract claim closed by
`prove_ensure_resource` (`src/surface/checking.rs:153`), which decides it
with `ResourceContext::satisfies_fact`
(`src/kernel/primitives/resource_algebra.rs:4887`) against the whole final
state, without consuming what it matched. `satisfies_fact` answers a memory
range from the cells a held composite supplies and a composite from its held
body, so the composite and its children each satisfy their own clause. The
joint check that would catch this
(`returned_resources_are_jointly_available`,
`src/surface/proof/claim_proofs.rs:4937`,
`state.resources().without_facts(checked_returned_resources.facts())`) only
feeds `checked_resource_transitions_by_path`; it does not fail the proof, and
`ResourceContext::without_facts` itself consumes a memory range out of a
composite that supplies it. The hole is specific to the default
`ResourceSemanticsMode::Legacy` (`src/surface/verification.rs:174`): under
`resource_semantics=authority` the joint receipt check
`resource_receipts_jointly_available` (`src/surface/proof/claim_proofs.rs:5`,
`without_fact_incrementally` over every receipt) refuses the minimal file, the `leak`/`h`/`caller` file and the `boxed`/`ticket` file with
`missing resource fact`, so the legacy branch (`legacy_grouped_transition`,
`claim_proofs.rs:4907`) is the one that lets a per-clause answer stand.
Compare also the entry side, where a call's
requirements are consumed as one multiset
(`resource_context_definitionally_contains`, `src/kernel/functions.rs:27504`)
and a call needing `pair(a)` to supply both itself and `cell(c)` is correctly refused with `missing owns pair(a)`.

## Reproduction

`leak` returns `wrap(p)` and `p[0..1]` from `wrap(p)`
alone. `h` owns `wrap(a)` and `b[0..1]` and writes `b[0] = 2` then
`a[0] = 1`; its claim `result == 2` is proved because the two owned facts
are taken as separate cells. `caller` holds only `wrap(p)`, calls `leak(p)`
to obtain the duplicate, then `h(p, p)`. Its claim `result == 2` is false:
`p[0]` is `1` when `h` returns.

```c filename=l34.c
int32 leak(int32* p) {
    return 0;
}
int32 h(int32* a, int32* b) {
    b[0] = 2;
    a[0] = 1;
    return b[0];
}
int32 caller(int32* p) {
    leak(p);
    return h(p, p);
}
```

```click
resource wrap(p: int32*) {
    owns p[0..1];
}
verifying "l34.c";
int32 leak(int32* p) {
    owns wrap(p);
    produces p[0..1];
} by auto;
int32 h(int32* a, int32* b) {
    owns wrap(a);
    owns b[0..1];
    ensures result == 2;
} by {
    step();
    unfold(wrap(a));
    execute();
    fold(wrap(a));
    simp();
}
int32 caller(int32* p) {
    owns wrap(p);
    ensures result == 2;
} by auto;
```

Observed:

```text
$ click verify repro.md
3 selected proofs verified
$ echo $?
0
```

Minimal form, also exit 0 with `1 selected proof
verified`:

```click
resource wrap(p: int32*) { owns p[0..1]; }
int32 f(int32* p) {          // C body: return 0;
    owns wrap(p);
    produces p[0..1];
} by auto;
```

Further shapes that verify for the same reason, each reproduced on
2026-10-07:

- `owns p[0..1]; produces wrap(p);` and
  `owns wrap2(p); produces p[0..1]; produces p[1..2];`;
- an abstract child: `boxed(a) { owns a->id; contains ticket(a->id); }`
  with `requires a->id == 1; owns boxed(a); produces ticket(1);`
 ;
- a child named through an owned cell, where the function also stores to
  that cell: `pair(a) { owns &a->next; contains cell(a->next); }` with
  `requires a->next == c; owns pair(a); owns cell(b); produces cell(c);`
  and body `a->next = b;` returns three exclusive resources from two
 ;
- a recursive `list` resource: `relink(a, b)` with `owns list(a); owns
  list(b);` and body `a->next = b;` returns `list(a)` (whose tail is now
  `list(b)`) beside `list(b)`; a caller then owns `b->value` directly while
  `poke(a)` flips it through `list(a)`, and proves the false
  `r == b->value` (3 proofs verified).

Controls: returning strictly fewer resources than the contract names is
refused (`missing resource fact`), and two
copies of one exact composite (`owns cell(b); produces cell(b);`)
are refused, so the hole is specifically a composite and its own body
children counted once each.

## Intended regression

Negative mdtests, each expected to fail with a missing-resource diagnostic
naming the clause that cannot be supplied:

- the minimal `owns wrap(p); produces p[0..1];` and its dual
  `owns p[0..1]; produces wrap(p);`, both `by auto`;
- the two-child `wrap2` form;
- the `boxed`/`ticket` abstract-child form;
- the `pair`/`cell` three-from-two form with and without the explicit
  `fold(pair(a))`;
- the `leak`/`h`/`caller` file above, expected to fail at `leak`.

Positive controls that must keep verifying: `owns wrap(p);` alone;
`consumes p[0..1]; produces wrap(p);` with `fold(wrap(p))`;
`consumes wrap(p); produces p[0..1];` with `unfold(wrap(p))`; and
`relink` with `consumes list(b)` instead of `owns list(b)`.

## Acceptance criteria

- The contract exit consumes the returned resource clauses from the final
  state as one multiset, so a composite cannot supply its own clause and a
  body child's clause, in either direction of expansion; a failed joint
  consumption fails the proof rather than only toggling the transition
  certificate.
- `satisfies_fact`-style per-clause answers remain available for
  observations but are not what certifies a resource return.
- The regressions above pass, existing positive proofs are preserved, and
  `scripts/check.sh` passes.
