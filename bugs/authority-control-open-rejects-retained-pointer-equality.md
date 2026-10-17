# Opening a shared-heap control rejects a retained pointer-value equality

Soundness: incomplete. A valid resource open is refused by the checked
resource-rewrite boundary. This reproduction does not show false acceptance.

Reproduces on `8d8a621cc`:

```sh
cargo build --bin click
cargo run --bin click -- verify --trace-proof parent_read_payload \
  mdtests/shared_heap_population_certification.md
```

The source and complete native C reproduction are in that existing mdtest.
`parent_read_payload` owns a parent link, `child_control(p->kid)`, and
`child_ref(p->kid)`. Its linked arm unfolds the parent, establishes the
entry child's identity, and opens `child_control(p->kid)` to read the payload.
The control owns the child's allocation, object, and reference authority.

The open is refused with:

```text
kernel rejected checked resource `open`
authority control introduced an unchecked pure fact:
ConditionIs(PointerValueEqual(CPointerValue { ... }, ...), true)
```

The complete pointer-value equality relates an external symbolic address to a
loaded pointer's designation. The trace records the preceding identity fact;
the failure occurs in the legacy allowed-fact reconstruction in
`CheckedResourceRewrite::check_authority_wrapper` in
`src/kernel/proof/execution.rs`. The producer/checker disagreement needs
reduction; its exact cause is not established. Do not accept arbitrary
successor facts or discard pointer designations to bypass the check.

The audit job of nightly run `39031661877` fails here for this fixture,
`shared_heap_population_lifecycles.md`, and `shared_heap_two_parent_caller.md`.
The first fixture's selected proof also fails locally before expansion, so
this is not solely an emitted-certificate problem.

Acceptance: these unchanged positive fixtures verify and their selected
`parent_read_payload` claims expand and recheck. Preserve the native C,
ownership contracts, pointer identities, and existing missing-reference,
double-release, and premature-free rejection controls. Follow the kernel's
construction-based operation boundary when repairing the legacy rewrite path.
