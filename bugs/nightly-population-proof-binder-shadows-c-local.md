# Population certification nightly proof shadows a C local

Soundness: not soundness. The verifier rejects the fixture during name
resolution; no false claim is accepted. The stale proof prevents the nightly
regression from reaching its population certification and expansion checks.

Priority: P2.

On master `e92c95864`, the unchanged nightly regression fails before its first
expansion:

```sh
cargo nextest run --lib --profile nightly --run-ignored only \
  -E 'test(=surface::tests::expansion_tests::authority_population_certification_expands_every_smart_site)'
```

It reads `mdtests/shared_heap_population_certification.md`, then its initial
`verify_c0_project` fails with:

```text
population.click:143: `kid` names a C variable here; a proof binder cannot hide it,
since execution keeps reading the program's `kid`; choose another name
```

The fixture uses `ParentLink::Linked(kid)` proof binders while the original C
functions also declare `kid`. Keep the original C source and resource claims;
update conflicting proof binder names and their proof-local references to
respect the resolver's existing restriction. Check all such binders in this
fixture rather than just the first diagnostic.

Acceptance: the original fixture verifies, and the named nightly test expands
and cold-rechecks every smart site successfully. Preserve the parent-detach
tautology and the population/resource transition that motivated the test.
