# Imported C contracts drop proof-inferred object-type premises

Soundness: soundness-adjacent. The unpublished nominal model-pointer work can
require an original-object-class premise when a C proof constructs a typed
model field. Its completed rule carries that premise, but an imported contract
is assumed from its declaration alone. A caller therefore bypasses a dependency
that combined verification enforces. No false observable C postcondition has
been established by this reproduction; the trust boundary and inferred callable
interface are inconsistent.

## Reproduction

The companion directory contains the unchanged minimal C and three sidecars.
With the nominal model-pointer feature enabled:

```console
click verify bugs/model-pointer-import-drops-type-premises/library.click
click verify bugs/model-pointer-import-drops-type-premises/caller.click
click verify bugs/model-pointer-import-drops-type-premises/combined.click
```

The first two commands succeed. The third rejects `caller` with:

```text
call to `wrapped` parameter `p` requires original object class `struct model_node` or null
```

`wrapped`'s declaration produces a token with an abstract `NodeRef` model and
no stated relationship to its argument. Its proof chooses `NodeRef::At(p)`;
that choice consumes the assumed original-object type of its formal `p`.
The inferred requirement becomes part of the completed kernel function rule.
`caller(void* p)` casts its argument to `struct model_node*` and calls
`wrapped`. Combined verification correctly refuses the unavailable premise.
When `wrapped` is imported, the scoped external rule retains the written
contract, but not that inferred premise, and the same caller proof succeeds.

The source alone currently does not state the extra precondition. Separate
verification cannot assume that a separately proved callee has a stronger
interface than its declaration without transmitting that interface.

## Acceptance criteria

- Separate and combined verification agree about the required object-type
  evidence at this call.
- Every premise needed by an imported checked contract is available from its
  callable interface, or that dependency remains explicit and unresolved.
- Body proof choices cannot silently strengthen an assumed source interface.
- Address-only casts and contracts retain their approved existing behavior.
- Keep a regression with a real import and separately checked helper; testing
  a completed rule in one combined sidecar does not cover this boundary.

## Repair in progress

The callable interface now derives nominal input requirements from the written
contract, not the proof body. The original `library.click` reproduction is
rejected at its body-only model construction, so it cannot supply a separately
verified implementation for the weaker imported declaration. The companion
sources retain the original failure pattern.

`mdtests/model_pointer_import_interface.click` separately verifies a helper
whose postcondition states the typed model relationship. The positive import
fixture uses that declaration successfully; the negative import fixture
rejects an unknown original class. All three pass in the full Markdown run.
The feature is still unpublished and other compatibility failures remain.
