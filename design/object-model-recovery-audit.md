# Shared object-model recovery audit: 2026-10-14

## Revisions and reproducibility

This is a fixed-baseline audit, not a green verdict for the accumulated model.

| Item | Revision or identity |
| --- | --- |
| Master baseline | `325f9f604` (immutable during this comparison) |
| Archived implementation | `b92deef95`; archive plus recovery plan `e3d84a785` |
| Preserved fork branch | [`codex/object-model-archive-2026-10-14`](https://github.com/lacker/click/tree/codex/object-model-archive-2026-10-14), pointing at `e3d84a785` |
| Published #646 at audit start | Open; `lacker:codex/initialized-byte-output` at `4d86a66e72e9a02f9f51107c77a268c7b08b4d57`; no auto-merge request or queue entry |
| Master worktree | `/workspace/click-object-audit`, `codex/object-model-baseline-audit` |
| First extraction worktree | `/workspace/click-object-pointer-values`; initially `325f9f604`; delivery rebased through `2010b27f1` to `b8f7a8ea1` |
| Verifier toolchain | rustc/cargo 1.98.1; mdBook 0.4.52; LLVM/Clang 19.1.7 |
| Rust import compiler | `nightly-2026-09-17`, commit `923c95cdf5ba65cea505aa2ea829f578e1506ed8` |
| Charon extractor pin | `5d6b812e5f77dbf3d7f66c21b9b57091f0e084cb` |
| Cargo.lock SHA-256 | `8ddfd94c170a27378392f305f6904f0114d9cf772e0624f38b19654d25833652` |
| Charon profile SHA-256 | `fe1d73e76ebabdf5d32230a27164dd2845782d05a395da8b649270ff3e2ccb1c` |
| Exporter schemas | Master 59; archive 60; each run uses its own revision's exporter |
| Master exporter SHA-256 | `8c4ee9ff0fe110603d18ff62c6b836ca34b4ba75b7fbb72bc2ce0ce1884c1f91` |
| Archive exporter SHA-256 | `d4ac8f2a4350400ab0a63a22f03126f5f525273f8bda6f16de02b0b011c4e29d` |

Latest remote master at audit start was `943b72c759cfa139585475a77d8de04ea857d569`.
The comparison deliberately stays on the master revision already integrated in
the archive; a later delivery must account for newer upstream changes separately.

All `examples/` C, C++, Rust and Click program/contract files are identical
between baseline and archive. The only tracked example-tree difference is
`marked-linked-list/README.md`. Both runs exercise the 52 normal projects;
the two existing nightly rbtree projects remain excluded. The archive harness
additionally implements the approved numeric-only marked-list rejection and
constructor-positive controls; those expectations are not treated as regressions.

## Commands and observed results

Baseline example comparison:

```sh
source /workspace/.click-tools/activate.sh
export CARGO_TARGET_DIR=/workspace/click-cpp-bytes/target
export CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 RUST_MIN_STACK=8388608
export CLICK_CPP_EXPORTER=/workspace/click-object-audit/target/cpp-exporter/click-cpp-exporter
cargo test --test examples example_projects -- --exact --nocapture
```

Result: **52/52 pass**, exit 0, 107.31 seconds for the harness. The baseline
was unmodified. `scripts/check.sh --ci-quality` also passes: formatting,
environment setup regressions, all-target Clippy, book build and structural
documentation lint. Vale is absent and its advisory prose lint is skipped.

The archive's latest compiled example executable was preserved before changing
Cargo revisions, then run with the archive exporter and the same exact test:

```sh
export RUST_MIN_STACK=8388608
export CLICK_CPP_EXPORTER=/workspace/click-object-design/target/cpp-exporter/click-cpp-exporter
/tmp/object-model-archive-examples --exact example_projects --nocapture
```

Result: **35/52 pass, 17 fail**, exit 101, 79.66 seconds. This reproduces the
prior archive result rather than comparing against an old log alone. The
executable SHA-256 is
`865e49098945a78e4810f83bb5d02827385a5e1dc696a7b5509f7fc99cf6b1c2`.
Its compiled manifest points to the archived worktree. Neither timing is a
performance claim; concurrent compilation and different search paths affect it.

### Normal-gate provenance

The initial baseline `scripts/check.sh` run exits 0, but it is **not a valid full
baseline verdict**. Its unit/import/CLI stage passes all 5,577 selected tests
(1,486 skipped). Concurrent extraction compilation subsequently replaces the
shared target directory's fixture binaries: those fixture logs identify
`/workspace/click-object-pointer-values`, rather than the baseline checkout.
A sequential fixture retry also reuses those artifacts and is interrupted.
Neither fixture result is credited to master.

Before the replacement run, stop competing Cargo builds and remove only Click's
package artifacts, preserving dependency caches:

```sh
# In /workspace/click-object-audit, with the environment above.
cargo clean -p clicklang
scripts/check.sh
```

The rebuilt baseline normal gate **passes, exit 0**: 5,577 selected unit,
import and CLI tests pass (1,486 skipped), all 52 normal example projects pass,
and the normal Markdown corpus passes. All fixture paths identify the baseline
checkout. The unit stage takes 191.305 seconds, examples 122.50 seconds and
Markdown fixtures 104.67 seconds. The total is 20m17s and emits the ten-minute
budget warning: the cold test compilation alone takes 9m09s, with another
3m39s for Clippy. This is a correct functional verdict, not an under-budget
run or a verifier performance claim. No limits or test selection are changed.
The archive's full normal gate remains unestablished; its example stage fails.

Check the compiled
manifest/fixture paths as well as the command's exit status. Never share
mutable Click artifacts between concurrent worktree builds when comparing
revisions. Prefer a separate `CARGO_TARGET_DIR` per concurrently built worktree;
when reusing a directory sequentially, remove the package's artifacts on a
revision switch and inspect the resulting paths. The independent baseline and archive example executables used in
the comparison above were tied to their correct checkout before switching
builds; their recorded 52-versus-35 result remains valid.

## Checked failure ledger

Every row below passes on fixed master and fails on the archive with the
unchanged source and claims. Classification is **branch verification regression**;
introducing commit and semantic cause remain unassigned. Similar errors suggest
reduction groups, not proven shared causes. Engineering owner is the shared
object-model recovery workstream. This records changed verification behavior,
not a conclusion that every previously accepted contract is sufficient under
the sound pointer laws. A demonstrated necessary semantic narrowing must be
recorded separately, with source-language evidence and explicit compatibility
accounting; baseline acceptance alone cannot establish that judgment.

| Project | Selected failure on archive | Required follow-up |
| --- | --- | --- |
| [allocated-linked-list](../examples/allocated-linked-list/allocated_linked_list.click) | `list_pipeline`: native composite body guard not established | Reduce and attribute; preserve original positive, expansion and retained checks |
| [arena](../examples/arena/arena_cells.click) | `arena_alloc.loop(1).preserve`: authority unavailable for `arena->data` | Reduce and attribute; preserve original positive, expansion and retained checks |
| [binary-tree](../examples/binary-tree/binary_tree.click) | observed child resource: missing `defined(old(*pointer))` | Reduce and attribute; preserve original positive, expansion and retained checks |
| [concurrency-fork-join](../examples/concurrency-fork-join/fork_join.click) | `fill_range` loop condition: required resource unavailable | Reduce and attribute; preserve original positive, expansion and retained checks |
| [detachable-buffer](../examples/detachable-buffer/detachable_buffer.click) | call transfer: native span lacks exact unresolved/loaded identity | Reduce and attribute; preserve original positive, expansion and retained checks |
| [heap-object](../examples/heap-object/heap_object.click) | `item_pipeline`: native composite body guard not established | Reduce and attribute; preserve original positive, expansion and retained checks |
| [input-cursor](../examples/input-cursor/input_cursor.click) | produced borrowing composite has no backing viewed call input | Reduce and attribute; preserve original positive, expansion and retained checks |
| [multifile-registry](../examples/multifile-registry/registry.click) | `registry_run`: invalid memory access | Reduce and attribute; preserve original positive, expansion and retained checks |
| [owned-segmented-buffer](../examples/owned-segmented-buffer/owned_segmented_buffer.click) | call transfer: native span lacks exact unresolved/loaded identity | Reduce and attribute; preserve original positive, expansion and retained checks |
| [owned-split-buffer](../examples/owned-split-buffer/owned_split_buffer.click) | call transfer: native span lacks exact unresolved/loaded identity | Reduce and attribute; preserve original positive, expansion and retained checks |
| [owned-string](../examples/owned-string/owned_string.click) | stored-element postcondition unavailable to `assumption` | Reduce and attribute; preserve original positive, expansion and retained checks |
| [owned-vector](../examples/owned-vector/vector.click) | stored-element and pointer-field frame postconditions unavailable | Reduce and attribute; preserve original positive, expansion and retained checks |
| [rbtree-augmented](../examples/rbtree-augmented/rbtree_erase_leaf.click) | `rb_erase_augmented`: `simp` did not retain a complete ensure proof | Reduce and attribute; preserve original positive, expansion and retained checks |
| [refcount](../examples/refcount/refcount.click) | `refcount_pipeline`: `auto` cannot prove `amount < obj->refs` | Reduce and attribute; preserve original positive, expansion and retained checks |
| [ring-buffer](../examples/ring-buffer/ring_buffer.click) | `ring_buffer_pipeline`: `normalize` does not establish the goal | Reduce and attribute; preserve original positive, expansion and retained checks |
| [rust-byte-sum](../examples/rust-byte-sum/sum.click) | deterministic smart-work budget exhausted at statement 63 | Reduce the work curve; retain the existing budget and original proof claim |
| [rust-chunks-exact](../examples/rust-chunks-exact/chunks.click) | loop preservation: pointer arithmetic leaves pointed-to object | Reduce and attribute; preserve original positive, expansion and retained checks |

The [existing pointer-field frame bug](https://github.com/lacker/click/blob/e3d84a785792c007da19d2f42d75b9e143372164/bugs/c-pointer-field-postconditions-lose-frame-evidence.md)
tracks the vector/string group. Other groups need reductions before filing new
bugs or choosing semantic changes. In particular, rbtree-augmented and refcount
are not master failures at this revision; the earlier unclassified report left
that question open.

## Attributed reductions and preserved repair checkpoints

PR [#937](https://github.com/clicklang/click/pull/937) merged the entry-read fold
repair; final pushed head `2ad128f94` is an ancestor of fetched upstream master.
This is an independent upstream delivery, separate from native-entry activation.

The [conditional-record reduction](../mdtests/conditional_allocated_record_output.md)
now has a preserved archive-based repair at `132cb424b` on
`codex/object-model-failure-reduction`. The original allocated-linked-list and
heap-object projects and the reduced producer/caller pass. Three kernel controls
retain strict-native and explicit-validity rejection; two selected C++ member
domain rejection fixtures pass. These targeted results do not constitute a new
full example-stage or normal-gate verdict.

The [C buffer output reduction](../bugs/native-span-output-loses-c-carrier.md)
passes fresh, expanded, rewritten and retained checking on the #937 delivery
and fails on both `e3d84a785` and `132cb424b`. A bounded probe distinguishes the
entry's unresolved carrier from the designation-free symbolic field observed
at output transfer. A reader-only change does not restore the original
project. A narrowly scoped resource-annotation compatibility experiment restores the
unchanged detachable-buffer project and the reduction in all four proof modes.
Split-buffer and segmented-buffer pass the identity-error point but still fail
at subsequent range folds; retain them as unresolved rows. Repair checkpoint `86abef177` on `codex/object-model-failure-reduction` preserves
the change and reduced regression. All 17 selected span/record kernel controls
pass, including explicit-validity, native-policy, known-domain bounds and
pointer-cell readability checks; the selected Markdown regression passes.
This archive-dependent checkpoint is not an independent upstream activation. Neither reduction
has an introducing commit assigned yet.

## Normal example-stage recheck of the repair tree

At repair checkpoint `86abef177`, the normal `example_projects` test checks the
same 52 projects with revision-compatible artifacts. It fails in 71.85 seconds:
38 projects pass and 14 fail. Comparing project names with the frozen archive's
17-failure ledger shows exactly three restored projects (allocated-linked-list,
heap-object and detachable-buffer), with no new failing project. This is an
example-stage result, not a full green gate.

```sh
source /workspace/.click-tools/activate.sh
scripts/build-cpp-exporter.sh
CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=1 RUST_MIN_STACK=8388608 \
CARGO_TARGET_DIR=/workspace/click-object-failure-reduction/target \
cargo nextest run --test examples -E 'test(example_projects)'
```

The binary reports fixture roots under `click-object-failure-reduction`; its
exporter is built from that archive-compatible tree. The remaining failed
projects are arena, binary-tree, concurrency-fork-join, input-cursor,
multifile-registry, owned-segmented-buffer, owned-split-buffer, owned-string,
owned-vector, rbtree-augmented, refcount, ring-buffer, rust-byte-sum and
rust-chunks-exact. The two buffer failures now occur at later range folds;
the other twelve retain their recorded failure categories. No limits,
quarantines, original programs or claims changed.

## Loop escape and retained-resource lookup recovery

The [loop selector reduction](https://github.com/lacker/click/blob/6b8c5a1bbf0ce3f79ffe9f5e2891ada0aa432b84/bugs/loop-resource-selector-loses-descriptor-read-authority.md)
attributes the erroneous `MemberAddress` escape classification to archived
commit `3e6d4cc0e7`. Preserved repair `6b8c5a1bb` keeps a pointer carrier stable
when selecting its referent's member, while retaining genuine escaped-slot havoc.
All seven selected loop-carrier tests pass. The unchanged concurrency-fork-join
project passes on this escape-only checkpoint.

A second reduced defect shows candidate-index disagreement: the existing argument relation accepts both
arguments, while the pointer-root index selects no holding. The preserved
candidate at `bd6659d9a` adds producer-read/frame identities to discovery and uses
the selected C-value arguments consistently in surface and kernel unfolding.
It depends on archived pointer-designation machinery and is not independently
landed object-model activation. Neither pointer equality nor typed-place validity
is weakened.

All 31 selected kernel controls pass. The new index regression bounds lookup work
below 100 units beside 16, 64, 256 and 1,024 unrelated loaded-pointer resources,
checks withdrawal, and rejects partial writes even with numeric address equations.
Both C++ member-domain rejection fixtures pass. Eight of nine selected
resource-unfold Markdown fixtures pass; the ninth retains its `6b8c5a1bb`
pointer-arithmetic rejection. The archived fieldless entry-fold rejection also
predates this candidate and is already fixed independently upstream by #937.

The normal example stage on `bd6659d9a` checks the unchanged 52 projects with
revision-compatible artifacts: **39 pass, 13 fail**, in 137.45s. No new failing
project appears relative to `86abef177`. Fork/join also passes fresh checking,
smart expansion, verification of the expanded source and retained-session
rechecking. Its restoration belongs to the earlier escape repair. The remaining
failures are the preceding 14-row list minus concurrency-fork-join; arena now
fails at a later control-budget limit. This remains an example-stage failure,
not a green full gate.

The original reduced loop now gets through retained unfolding and fails later
at its post-store range fold. Preserve that original positive and its later
failure; do not credit a complete repair from the newly restored intermediate
step. Continue with checked pointer-field frame/range transport, with unchanged
work limits, C and claims.

The follow-up preserved checkpoint `bcb416098` retains publication-time read
keys per entry, so withdrawal stays exact after a later producer frame edge
changes canonicalization. The multi-size lookup regression and the dedicated
late-edge withdrawal test pass. This is a withdrawal-only safeguard; the full
example-stage verdict above remains attached to `bd6659d9a`.

## Independent defect and extraction candidate

Master rejects a resource owning `p[0]` when its pointer argument is substituted
with a complete captured value. It reports `a pointer operation has no known
pointee type`. The archive accepts the same small C program:

```c
int32 probe(int32* p, int32 input) {
    p[0] = input;
    return input;
}
```

```click
resource cell(p: int32*) { owns p[0]; }
int32 probe(int32* p, int32 input) {
    owns cell(p);
    ensures result == input;
} by { unfold(cell(p)); execute(); fold(cell(p)); simp(); }
```

The extraction adds only
`CExpression::Value(value) => value.c_type().pointee_type()` to the existing
pointee-type lookup. It requires no new pointer representation, profile,
initialization effect, importer schema or keyword. The existing complete value
supplies its type; access checks still decide storage authority and validity.
The positive and view-only write rejection are separate focused Markdown
regressions. The extracted patch is committed as `11d9f44b9` on the clean-baseline branch
`codex/object-model-pointer-values`, not cherry-picked with the surrounding
object-model activation. The same patch rebases cleanly onto current upstream
`2010b27f1` as `1b695539d`; delivery checks on that revision are separate from
the frozen baseline comparison. Its positive and view-only rejection both pass. The
positive also passes fresh verification, expansion, rewritten verification and
retained rechecking. All-target Clippy passes. The normal example run passes
51 projects and fails only because that worktree lacks its local C++ exporter;
after building that exporter, the focused `basic-cpp` rerun passes. These checks
cover all 52 projects but are not a single full green-tree run.

Alignment-result typing is **not** an independent candidate at this baseline:
`PointerAligned` itself belongs to the accumulated branch. Entry-argument folding
also needs a separate dependency/reproduction audit. Those are not bundled into
the first extraction merely because they shared a historical commit.

### Delivery checks

The extraction rooted at `2010b27f1` passes all 52 normal example projects and
3,752 normal Markdown fixtures, including both new captured-pointer controls.
The fixture stage exits 0 in 291.844 seconds; all fixture paths identify the
extraction checkout. Documentation tests initially pass 36/37 and reject one
retired execution-engine word in this audit; the prose is corrected without
changing the terminology check.

Upstream then advances to `b8f7a8ea1`, including contract-syntax and expansion
changes. The two-commit extraction rebases cleanly onto it; its typing commit is
`abdd5c64f`. On that updated delivery revision both focused Markdown controls pass
(0.18 seconds for the harness), all 37 documentation checks pass, and the
positive proof passes fresh verification, expansion, rewritten verification
and retained rechecking. Formatting, book build and documentation lint pass.
The corresponding command sequence exits 0. Required CI and the merge queue supply the
full delivery-tree gate; the earlier full verdict belongs to fixed `325f9f604`.

Commands for the updated delivery checks, run sequentially in the extraction
worktree with its own exporter and the pinned toolchain:

```sh
cargo clean -p clicklang
cargo fmt --check
MDTEST_FILTER=captured_pointer_cell cargo nextest run --test mdtests --no-capture
scripts/check.sh --docs-only
cargo build --lib
```

The expansion check uses the public APIs
`expand_project_claim_source_by_label`, `verify_c0_project`, and
`C0VerificationSession::verify_at_project` for `probe.contract`, rechecking the
expanded source in both fresh and retained state.

## P1 soundness recheck

The ordinary C reproduction in
[the scalar-subobject bug](../bugs/pointer-arithmetic-crosses-scalar-subobject.md)
still verifies incorrectly on both `325f9f604` and `e3d84a785`:

```c
struct Pair { int32 first; int32 second; };
int32 probe(struct Pair* p) { return *(&p->first + 1); }
```

The sidecar is:

```click
verifying "probe.c";
int32 probe(struct Pair* p) {
    views p->first;
    views p->second;
    ensures result == p->second;
} by { execute(); simp(); }
```

Both probes exit 0. Under C11's one-element scalar domain,
one-past `first` cannot be dereferenced to read `second`. The defect is still P1;
passing native/C++ controls must not be advertised as closing ordinary C.
The small typing extraction does not fix this soundness gap and must not claim
object-model completion. Its required repair needs the dependency closure of
source pointer production, designation transport and checked access, or an
explicit sound refusal that preserves legitimate source patterns.

## Change inventory and dependency boundaries

The comparison `git diff --numstat 325f9f604..e3d84a785` includes the recovery
plan commit, so it has 250 changed paths rather than the implementation
checkpoint's 249.

| Area | Changed paths | Added lines | Removed lines |
| --- | ---: | ---: | ---: |
| Design, documentation and backlog | 27 | 2498 | 41 |
| Other tools/integration metadata | 5 | 297 | 31 |
| Tests and proof fixtures | 23 | 1911 | 93 |
| CLI and audits | 4 | 69 | 45 |
| Shared kernel | 98 | 43280 | 1926 |
| C adapter | 4 | 1838 | 320 |
| C++ adapter | 11 | 2014 | 75 |
| Rust adapter | 4 | 345 | 36 |
| Contracts, proof, diagnostics and surface | 74 | 10748 | 3342 |

This is a responsibility inventory, not permission to split by directory:

1. **Independent type observation fix:** the captured-value case above; no
   activation dependency. Prepare the first green delivery with paired checks.
2. **Initialization/construction/representation:** shared initialization ranges,
   destination binding, completion, copies, lifetime events and the uint32 byte
   bridge touch execution and modular summaries. Identify already landed pieces
   before extracting remaining operations and their complete proof checks.
3. **Pointer model:** domains, full-value equality, pointer-valued cells and
   pointer/integer transport have coupled producers and consumers. No half-model
   that stores designation but loses it through substitution or calls can be
   called sound. Ordinary C's reproduced failure remains part of that closure.
4. **Native entry/call/resource activation:** the new `native_record_inputs`,
   `native_span_inputs`, pointer-result effects and contract lowering rely on
   those pointer laws. The 17 compatibility failures must be attributed here or
   elsewhere before enabling the affected profile in an extracted delivery.
5. **Frontends and pinned models:** C++ schema/library changes require matching
   importer validation, kernel support and profile-specific controls. C/Rust
   adapter changes cannot be pulled in as incidental fixes without their
   unchanged-source comparison and own admission evidence.
6. **Proof tools and audits:** source synthesis, snapshots, retained rechecking and
   instrumentation must agree with the selected semantic slice. Extract
   standalone defects where reproduced on master; keep semantic identity and
   certificate compatibility changes with their corresponding kernel change.

First code introduction for several pointer/entry modules is checkpoint
`55238f40b` (a WIP integration commit), followed by multiple repairs and merges.
That commit is a starting point for attribution, not a proposed delivery unit.
A new bisect must preserve original source/profile and avoid reporting build
failures as proof regressions.

## Completion ledger

- [x] Archive published to the fork; original PR state and immutable comparison
  revisions recorded; primary checkout and baseline source left untouched.
- [x] Compare all normal example projects with identical source/contract files.
- [x] Record all 17 branch failures and one independent master defect.
- [x] Recheck the ordinary C scalar-subobject P1 reproduction on both revisions.
- [x] Record a responsibility inventory and conservative dependency boundaries.
- [x] Establish the fixed master's normal-gate result with correct artifacts.
- [ ] Establish the archived candidate's full normal-gate result; its example
  stage is already a reproduced failure.
- [ ] Attribute the introducing changes for the 17 failures with reductions or
  bisect; choose the minimal sound pointer-activation closure.
- [ ] Complete and publish the first isolated green extraction; settle #646's
  replacement only after that result is concrete and the archive is linked.

Command logs for this session are in `/tmp/object-model-*.log`; commands,
revisions, error summaries and the small reproductions above remain committed
so the audit does not depend on those transient files.

## First delivery and follow-up reductions

PR #926 merged through the queue in `16f0d77df`, including final pushed head
`3043ac0a7`. Its corrected typed/untyped unit controls and all 5,198 selected
library tests pass. The independent entry-fold extraction captures entry-valued
arguments once and returns the exact selected resource to its kernel check.
The unchanged fieldless entry-argument proof is a compatibility control; a
second interpretation previously selected a different representation.

The rebased entry-fold slice on `7920aaf0e` passes all 52 normal examples,
3,764 Markdown fixtures, 37 documentation checks and all-target Clippy. Plain
and nested indexed-cell proofs and the existing fieldless entry proof pass
fresh, expanded, rewritten and retained checking. Wrong-cell controls reject.
The reduced C indexed-cell contracts use the existing viewed range; no unmerged
object-model activation is included.

The [conditional-output reduction](../mdtests/conditional_allocated_record_output.md)
attributes the allocated-list/heap-object error group to a native composite
formation check demanding a decided guard on a verified conditional output.
The small producer/caller passes baseline proof modes and fails on `e3d84a785`.
A setter-shadowing experiment did not fix the original list and was discarded.
The defect never reached master; the reduction is now a master regression
fixture, so any object-model activation must keep this producer/caller passing.
Checkpoint `132cb424b` repairs only conditional heads without native promises;
a guarded native promise with an undecided guard still needs admission under
its guard before activation.

## Backing-range fold reduction after the read-index safeguard

A fresh local investigation of the original descriptor/loop reduction on
`bcb416098` confirms the later post-store fold rejection. At incremental memory
consumption, a temporary bounded probe reports zero indexed candidates; the
unchanged entailment comparator accepts the one held backing owner among the
three held memory facts. Its bounds and stride match the requested range, but
its producer pointer-read variable differs. The cheap recorded-equality query
returns false for the pair. Ordinary coverage therefore recognizes a checked
relation that candidate discovery does not select.

This is an attribution result, not a repaired proof or a new example-stage
verdict. The probe is removed from production; no ambient scan, equality rule,
origin privilege, source change or work-budget change is retained. The next
small repair should cover this selected relation in indexed memory lookup,
with scaling and authority-withdrawal/partial-write controls. Details remain
in the preserved [descriptor-backed loop witness](../mdtests/loop_resource_backing_range_fold_after_write.md).

## Certified footprint-query endpoint slice

Recovery checkpoint `bca4dafb8` selects the queried producer read's endpoint
through a bounded complete-cell walk, checks the retained certificates, and
uses the resulting numeric union only for footprint candidate selection.
Concrete read-permission queries retain their completed-read boundary. A stopped
unproved/affecting write keeps an opaque read at that snapshot; its cached old
value cannot authenticate transport. The accompanying signed-order check accepts
intrinsic forward constant connections before/between retained premise steps,
including the `1 < 2 <= n` witness, without admitting symbolic or reversed gaps.

All **84** selected recovery memory-index, pointer-designation, native-span,
loop-carrier and order-certificate tests pass. The scaling witness checks 16,
64, 256 and 1,024 unrelated loaded-pointer ranges with query work below 2,000,
and checks owner/frame withdrawal, partial writes and caller-graph isolation.
The original recovery loop still fails at its post-store fold. An earlier
prototype's apparent success depended on reusing a cached value at an unproved
write; the withdrawal control exposed that shortcut and it is removed. No new
full example-stage verdict is claimed, and the residual read-chain gap still
needs attribution.

The independent master extraction on base `bdb6636fd` passes **59** selected
memory-index/order-certificate controls, the original source-level loop and both
existing byte/word partial-pointer-write fixtures. The loop passes fresh,
expansion, rewritten and retained checks; all **37** documentation checks pass.
This extracts a shared checking/lookup prerequisite without activating the larger
object model or claiming the archived original loop repaired.

The delivery is rebased onto `14746f449`; the same 59 selected kernel controls
pass again (6.51s for the harness). This rebase does not change the archived
candidate or credit its unresolved original loop.

## Loop-havoc borrow-partition producer repair

Recovery checkpoint `53da27b58` identifies and repairs the reduced loop's final
read-chain gap. A bounded producer probe shows a certified backing-store frame,
followed by a stop at the checked loop-havoc summary. The range-disjointness
producer omitted the live borrowed-view/owner partition even though its checker
already accepts that authority. Select it by the two queried address keys before
the legacy ownership-composition frontier, retain the complete range/access
memberships, and recheck the composition authority and non-overlap.

All **87** selected memory-index, pointer-designation, native-span, loop-carrier
and borrow-frame controls pass (6.42s for the harness). The new witness bounds
selected producer work below 200 beside 16, 64, 256 and 1,024 unrelated owners;
it rejects widened reads, overlap, ordinary/view-only compositions and withdrawn
retained authority with a stale candidate index. The original C loop passes
fresh checking, expansion, verification of the rewritten proof and retained
rechecking with the safe endpoint rule. The diagnostic probe is removed.

This is a preserved recovery implementation, not an upstream activation. At
that checkpoint master had the independent footprint-query slice from merged
PR #969; the range-frame certificate prerequisite still needed extraction.

The broader example-stage run was interrupted by the environment outage; its
temporary log was lost on restart. No new full example-stage verdict is claimed.

## Upstream loop-havoc borrow-partition extraction

The independent master extraction adds `BorrowPartitionRangeEvidence` to the
existing typed range-frame checker. The producer selects the live borrowed
view/owner partition through the queried addresses before searching ambient
separation facts. The certificate retains the composition and both members;
checking requires live authority, exact-arithmetic containment of the complete
mutable footprint, full-access read membership and no overlap under current
address equalities. This slice uses existing containment and access rules;
it imports no archived native-object declarations or general range-search
machinery.

The focused witness reproduces a missing certificate on unchanged master and
checks the repair through an actual `LoopHavoc` equality certificate. Producer
work is 22 units beside 16, 64, 256 and 1,024 unrelated owners. Widened reads
and footprints, overlapping addresses, stale indexes after authority withdrawal,
unbound views and view-only compositions reject. The original C loop remains in
[`loop_resource_backing_range_fold_after_write.md`](../mdtests/loop_resource_backing_range_fold_after_write.md),
with a regression covering fresh checking, expansion, rewritten checking and a
retained session. This extraction completes the remaining borrow-frame slice of
the retained-resource lookup repair; broader object-model activation remains
separate.

## Full-width explicit-separation integration

While PR #987 was open, upstream `3b0550fbc` independently delivered the bounded
borrow-frame producer and its actual-loop equality/expansion controls. Reconcile
#987 with that implementation and keep the upstream boxed borrow certificate and
its stronger overlap/widened-footprint tests. The remaining delivery changes only
explicit-separation frames: retain the two selected members and full-width read
membership in a boxed certificate, authenticate the live fact and full mutable
footprint when checking, and select candidates through address-indexed buckets.

The previous explicit-separation certificate checked only the starting address.
The regression rejects a read that starts in the final descriptor cell and extends
past it, an enlarged mutable footprint, and a withdrawn separation fact. Its
multi-size witness checks bounded, identical producer work beside 16, 64, 256 and
1,024 unrelated separation facts. Symbolic ordered-subrange and after-end evidence
remain separate recovery candidates; this repair uses existing exact arithmetic.

On the rebased implementation, all 149 selected frame/index/borrow kernel controls
pass (7.85s harness). Both focused explicit-separation controls pass after adding
a concrete overlap witness: a read [4, 8) is separate from mutable bytes [8, 12),
while a read [4, 12) must not frame that mutation. The selected upstream
`descriptor_backing_range_loop_survives_all_proof_modes` test passes (2.12s),
covering fresh verification, expansion, rewritten checking and retained rechecking
of the unchanged C/proof. The full nightly suite was not run.

## Completed post-loop-repair example audit

Checkpoint `53da27b58` completes the example-stage run lost during the outage:
**39 of 52 pass, 13 fail**, in 111.28s (nextest harness). The failed project set
is identical to `bd6659d9a`: arena, binary-tree, input-cursor, multifile-registry,
owned-segmented-buffer, owned-split-buffer, owned-string, owned-vector,
rbtree-augmented, refcount, ring-buffer, rust-byte-sum and rust-chunks-exact.
There are no restored or newly failing projects. Examples and the example-test
harness have no changes between those two revisions. This is not a green gate.

```sh
source /workspace/.click-tools/activate.sh
CARGO_BUILD_JOBS=1 RUST_MIN_STACK=8388608 \
CARGO_TARGET_DIR=/workspace/click-object-failure-reduction/target \
CLICK_CPP_EXPORTER=/workspace/click-object-failure-reduction/target/cpp-exporter/click-cpp-exporter \
cargo nextest run --test examples --no-fail-fast -E 'test(example_projects)'
```

The fresh original segmented-buffer trace leads to the complete
[modular buffer reduction](../mdtests/modular_buffer_ranges_rejoin_after_field_preserving_calls.md).
All three reduced proofs pass on the upstream-based `73cff194e` verifier. The
archive rejects the final fold: the held prefix and tail use descriptor pointer
reads from different call snapshots. Field-preservation equalities are present;
the precise missing checked frame/transport step is not yet attributed. Keep
native pointer-origin checking intact and diagnose that certificate path before
extracting additional general range rules. The split-buffer failure still needs
an independent reduction before claiming the same cause.

## Checked-coordinate buffer join repair

Archive checkpoint `477784302` restores both original buffer projects without
changing their C or claims. The selected pointer read has a checked, full-width
endpoint through the call frame. Candidate lookup uses that endpoint in a
query-local address graph, but scratch normalization previously reinserted the
original supplier ranges and lost their common coordinates. The repair restates
only selected byte-footprint suppliers in the query's checked coordinates before
joining them. It publishes no equality and changes no object designation,
validity, pointer-origin rule, or loan/support exclusion.

Validation on that implementation:

- All 86 selected memory-index, pointer-designation, native-span, loop-carrier
  and borrow-partition kernel controls pass (8.12s harness). The new regression
  fails before the repair and passes afterward. It rejects withdrawn separation,
  missing ownership and a partially overwritten pointer field; measured selected
  work stays bounded beside 16, 64, 256 and 1024 unrelated owners.
- The unchanged reduced bug and both original segmented/split-buffer pipelines
  pass fresh verification, expansion, rewritten checking and retained rechecking.
  The helper was explicitly relinked after `cargo build --lib`; an earlier helper
  invocation had used a stale top-level library artifact and is not evidence of
  a proof-mode disagreement.
- The normal 52-project example stage completes in 130.78s: **41 pass, 11 fail**.
  Segmented-buffer and split-buffer are restored; there are no new failures.
  Remaining failures: arena, binary-tree, input-cursor, multifile-registry,
  owned-string, owned-vector, rbtree-augmented, refcount, ring-buffer, rust-byte-sum
  and rust-chunks-exact. The gate remains non-green; no full nightly run was made.

This is a preserved archive repair, not activation of the archive. The next
step is to assess whether this small supplier-coordinate repair has independent
upstream value and can be extracted with its checked-frame prerequisites, then
continue reducing the remaining compatibility failures.

## Interior-write query follow-up

PR #1011 merged the supplier-coordinate join repair; its pushed head
`f2b2962a3` is verified in upstream history.

The modular-buffer range-join report is closed on current upstream. Its
unchanged reduction is preserved in
[`modular_buffer_ranges_rejoin_after_field_preserving_calls.md`](../mdtests/modular_buffer_ranges_rejoin_after_field_preserving_calls.md).
`modular_buffer_ranges_rejoin_in_all_proof_modes` checks that reduction and
both original segmented/split-buffer pipelines fresh, after expansion, through
independent rewritten-source verification, and in retained sessions. All 61
selected memory-equality-index tests pass, including the full-width adjacency
refusal and framed-fragment rejection/scaling controls at 16/64/256/1024
unrelated owners. The normal example stage passes all 50 selected projects;
the three nightly rbtree projects and the C++ example are excluded (the pinned
C++ exporter is unavailable in this environment). These are current-upstream
results; archive activation and its remaining compatibility failures stay in
this recovery audit.

Recovery checkpoint `c6d5c4200` then repairs a separate indexed lookup gap:
scalar interior-write queries must ask for the checked endpoint of producer-registered pointer-read prefixes, as
footprint queries already do. It keeps the relation query-local and checks the
live supplier's ownership and bounds. All 87 selected recovery kernel controls
pass (6.75s harness), including the original manual-snapshot rejection and a
failing-before/passing-after interior-write regression at 16/64/256 unrelated
owners. The regression rejects weakened separation, removed ownership, partial
pointer overwrites and a write past the owned extent.

This does not yet restore owned-string or owned-vector. Fresh verification still
rejects their original postconditions. The [two-store C reduction](../mdtests/pointer_field_reloaded_backing_writes.md)
also still rejects its second write, so execution-side pointer reload/authority
tracking remains the next reduced investigation. No C, contract, proof, tactic
budget or language-profile change is included in this checkpoint. No new full
example-stage count is claimed; the last completed audit remains 41/52.

The independently extracted query-prefix repair also passes all 63 selected
current-upstream controls (8.33s harness). It uses upstream's existing typed-load
API and omits the archive-only frame-context adapter. Formatting, book rendering
and structural documentation lint pass. The full gate and nightly suite were not
run locally; required CI supplies the integration verdict.

## Scoped program-read endpoints

Recovery checkpoint `a1cf07a24` repairs the execution-side two-write reduction.
A complete program read retained its certified binding in `PureFactContext`,
but endpoint lookup recognized only shared logical-read registrations. Publishing
that binding globally made an existing sibling-context rejection fail; the
repair instead selects its exact raw value from one unambiguous retained source
in the current context. The existing endpoint checker then checks the full
pointer cell and frame, and only the selected query graph receives the address
relation. Import rejects non-pointer or non-eight-byte producer bindings.

Retained rechecking exposed a second dependency: the live load-name registry can
name a different source from the binding saved with the proof. Lookup therefore
uses the retained source directly, without a registry round trip or source
search. Ambiguous source sets refuse. No object representation, designation,
lifetime rule, native validity promise or public keyword changes.

All 133 selected recovery load/index/designation/span/loop/borrow controls pass
(9.77s harness), including plain-proposition and missing-ownership rejection,
sibling isolation, and a test restoring an older naming registry. The unchanged
C reduction now admits both writes. Its regression proof adds one explicit
`have owner->data[0] == value by { simp(); }` for the stored-value postcondition;
C and claims remain unchanged. This positive passes fresh, expansion, rewritten
and retained checking, with a freshly rebuilt/relinked library. A wrong-value
postcondition is rejected. Temporary instrumentation is removed.

The execution-gap bug is replaced by
[`pointer_field_reloaded_backing_writes.md`](../mdtests/pointer_field_reloaded_backing_writes.md).
The original string/vector postconditions remain under the
[separate report](https://github.com/clicklang/click/blob/439b841c4633c9282354e772ffdf95748fb5dc41/bugs/c-pointer-field-postconditions-lose-frame-evidence.md).
The last full recovery example count remains 41/52; no new full-stage or nightly
verdict is claimed. PR #1016 merged and its pushed head `863de60ed` is verified
in upstream history.

The current-upstream extraction passes all 102 selected load/index/span/loop/borrow
controls (9.04s harness), including the scoped-binding and restored-registry
regression. It uses upstream's existing pointer-load kind and checks its complete
eight-byte width; no new scalar kind is introduced by this extraction.

The filtered upstream Markdown fixture passes (0.79s fixture time). It is in the
nightly list to preserve the normal gate's half-second fixture threshold; the
fast scoped-binding kernel regression remains in the normal suite. The focused
fixture was run explicitly; the full nightly suite was not run.

The current-upstream fixture also passes fresh verification, expansion, rewritten
verification and retained rechecking after an explicit `cargo build --lib` and
helper relink. The final filtered nightly-fixture rerun passes (1.02s harness).

### Explicit stored-value proofs in the original examples

Following PR #1023, `owned_string_set` and `vector_push` can discharge their
original contracts by explicitly proving relevant equalities before folding
their resources. The setter proves its stored value with `simp`; vector push
proves the unchanged backing pointer and the stored value. The existing final
`assumption` steps then consume those checked facts. C, claims, resource
contracts and kernel rules are unchanged.

The focused checks use the original functions in their full sidecars. Reduced
projects copy the same C, resource definitions, contracts and proofs for fresh,
expanded, rewritten and retained checks without admitting the unrelated failing
functions. This is partial recovery, not closure of the
[string/vector report](https://github.com/clicklang/click/blob/439b841c4633c9282354e772ffdf95748fb5dc41/bugs/c-pointer-field-postconditions-lose-frame-evidence.md):
string push still rejects its terminator equality, while the vector project now
reaches an allocation-resource fold in `allocated_vector_push`. The last full
archive audit remains 41/52; no new full-stage verdict is claimed.

Recovery checkpoint `d6caff076` preserves these proof changes and the updated
bug report. Both reduced cases pass all four modes on that checkpoint; both
wrong-stored-value controls are rejected. PR #1023's final pushed commit
`4df6468ff` is verified in upstream history before beginning this extraction.

With the CLI and library rebuilt at upstream `42315e69f`, both functions verify
in their original full sidecars. The two reduced projects pass all four modes,
and both wrong-value controls reject. mdBook, docs lint and whitespace checks
pass; Vale is unavailable, so its advisory prose lint is skipped. No full gate
or nightly suite was run locally.


### String push proof and full upstream project checks

PR #1027 merged, and its final pushed commit `bd36007a1` is verified in upstream
history. The next proof-only adjustment explicitly checks string push's unchanged
backing pointer and proves the unfolded zero terminator with `simp` instead of
requiring it to be an exact available fact. No C, contract, resource or kernel
changes are involved.

On the current upstream kernel, the complete owned-string sidecar verifies all
15 proofs and the complete owned-vector sidecar verifies all 13 proofs. The
whole string project also passes fresh verification, expansion of
`owned_string_push.contract`, rewritten-project verification and retained
rechecking. Controls with a wrong terminator or wrong appended value are rejected
at their final postconditions.

This corrects the earlier attribution: string/vector failures described in the
previous checkpoint are recovery-archive results, not current-upstream results.
At archive `d6caff076`, the same explicit backing-pointer proof still fails
after the zero store, with distinct projected pointer-read snapshots in the
trace. The archive's later vector allocation fold also remains open. The
[bug report](https://github.com/clicklang/click/blob/439b841c4633c9282354e772ffdf95748fb5dc41/bugs/c-pointer-field-postconditions-lose-frame-evidence.md) records
that distinction. Its activation work and the last full archive count of 41/52
remain unchanged. No new full example-stage or nightly verdict is claimed.

The entire vector project also passes fresh verification, expansion of
`vector_push.contract`, rewritten-project verification and retained rechecking.
The production kernel sources are unchanged between the explicitly rebuilt
`42315e69f` and this slice's upstream base `8fc1b58a7`; intervening changes are
coverage prose, #1027's proof adaptations and recovery records. Recovery
checkpoint `87ad14e1b` preserves the comparative failure evidence without keeping
the unsuccessful archive proof edit. mdBook, docs lint and whitespace checks
pass (Vale unavailable; advisory prose lint skipped).

### Split-field terminator reduction

PR #1028 merged; its final pushed commit `f669cb90f` is in upstream history.
The recovery reduction now preserves the original separately owned descriptor
fields. A whole-struct resource is a passing control but differs from that
original boundary. Explicitly establishing the nonnegative append index lets
the complete-width frame prove the unchanged pointer. Stored-value and zero
terminator facts also check. This needs no new object rule or keyword.

At checkpoint `ee9b29f87`, the next simple fold exhausts its unchanged
750,000-unit budget. The archived
[fold defect](https://github.com/lacker/click/blob/ee9b29f87822302f753f53eeb1c505bcc06f21ea/bugs/split-descriptor-fold-exhausts-simple-budget.md)
records its reproduction and incomplete diagnostic profile. The
[repair below](#preliminary-byte-gap-query-repair) supersedes this blocker. Repeated offset/range reasoning dominates the failed fold; a specific
performance repair has not yet been established. Failed proof edits and private
probes are removed from production sources. Keep the original 41/52 archive
audit and the separate vector allocation-fold failure open.

Archive checkpoint `ee9b29f87` preserves the executable Markdown reproduction
and updated reports. Its checked-in reproduction independently fails at the
same simple fold with 750,001 units; the original example source is restored,
and the CLI/library are rebuilt without probes. This is an unresolved defect
checkpoint, not a claimed fix or a positive archive verification result.

At upstream base `5fa772724`, a freshly rebuilt CLI/library verifies the focused
split-field fixture in 2.91s. Fresh verification, expansion, rewritten checking
and retained rechecking all pass. Wrong-value and wrong-terminator controls fail
at final postconditions; a control without backing ownership is rejected while
checking its resource's read authority. The filtered Markdown harness passes
(2.77s); the fixture is classified nightly, and only this named fixture was run.
No kernel rule or diagnostic presentation changes are included in this slice.

### Bounded resource-query shortcuts

A separate cleanup classifies literal resource quantities directly as signed
int32 values, retaining the existing bounded decision route for symbolic
quantities. A view-occurrence query returns immediately when the maintained
ownership count establishes that every held fact is owned; mixed inputs skip
owned candidates before aligning viewed requirements. These shortcuts neither
publish pointer equalities nor grant authority.

All 12 selected current-upstream quantity, view-dependency and fold-body controls
pass (0.50s harness). The new deterministic controls cover 0, 16, 64 and 256
unrelated facts/owners, signed count boundaries, symbolic counts, and view
insertion/removal/forks. This is not the archive fold repair: the same fold
still exhausts its budget. Private probes narrow that failure to lowering the
`terminated_at` body fact, after the preceding exact bound checks succeed.
PR #1038 merged, and its final pushed commit `e3175f36b` is verified upstream.

The cleanup's rebuilt upstream CLI/library also pass the split-field fixture's
fresh, expanded, rewritten and retained checks. Its filtered nightly-fixture
harness passes (3.14s). Formatting, mdBook, docs lint and whitespace checks pass;
Vale is unavailable, so advisory prose lint is skipped.

### Preliminary byte-gap query repair

PR #1042 merged; its final pushed commit `f3f71a8d7` is verified in upstream
history. The next archive repair targets the split-field fold itself. A private
stack sample identifies general signed-order reasoning inside the preliminary
byte-gap check: resolving its load operands reenters the same memory histories.
Use exact recorded order and indexed traversal of written order edges for that
directional check. The traversal retains only its successful path's exact
premises, handles order withdrawal, and performs no memory equality queries.
Unknown geometry falls through to complete range-separation evidence; constant-gap
and direction-free stride checks retain their behavior. The experiment moving
frame discovery out of read registration is excluded from this repair.

The archive's focused original-source proof now verifies at unchanged limits;
a completed profile measures its fold at 0.40s. Other expensive simple steps
remain and this is not a whole-proof performance claim. All 227 selected archive
memory-history, pointer-frame, designation, span, loop, loan and resource-query
controls pass. The new query regression checks 0, 16, 64 and 256 unrelated facts,
order withdrawal, absent/reversed order and overlapping access widths. The final
extraction also checks a two-edge order chain over memory-load atoms, preserving
the existing derived-order store-hop control. Wrong
stored-value and wrong-terminator claims reject, and missing backing ownership
is refused while checking the resource's read authority.

The initial exact-order variant's rebuilt probe-free archive CLI/library passes
fresh verification, expansion, rewritten verification and retained rechecking.
Archive checkpoint `be001cb2f` contains that initial repair; `3279dd7b0` preserves the separately checked push/pop proof
adaptations and the missing final-assumption trace reproduction.
The final indexed-order variant passes the split-field fixture and full original
owned-string project in fresh, expanded, rewritten and retained modes on both
the recovery archive and current-upstream extraction. Wrong stored-value and
wrong-terminator claims reject, and missing backing ownership is refused. These
checks close the fold-budget defect; its historical reproduction remains in
archive history. The separate returned-resource performance report remains open.

### CI graph-lock boundary follow-up

PR #1051's bounded order checks expose an existing graph reentry path in
`equivalent_field_derived_bases_frame_symbolic_index_store`. The failed library
partition reproduces locally: 944 of 945 tests pass and that case times out.
A debugger shows the graph mutex held by address registration while term
canonicalization starts a cell-epoch walk that queries the same mutex.

The repair keeps term interning and affine decomposition structural. Scalar and
offset query adapters perform selected normalization before locking; internal
raw-read names retain their exact snapshot, kind and access width. A new
multi-size raw-read registration regression complements the existing
snapshot/support and complete-width controls. The selected offset adapter
preserves expression shape while normalizing scalar indices before locking.

After integrating upstream `c819a273e`, all 5,415 normal library tests pass
(115.1s; 572 skipped), as do all 168 selected C++ import/span integration tests
(32.4s). All 534 selected archive graph, memory, designation, span, loop/loan and
diagnostic controls pass. Freshly rebuilt libraries and CLIs pass the positive
four-mode checks above; all three negative controls reject. Formatting, mdBook,
docs lint and whitespace checks pass. The full gate and nightly remain CI work.

The recovery archive's full original string project and focused original pop
and clear reductions now pass all four proof modes. Checkpoint `5570f876c`
preserves the one-line clear predicate elimination and the completed normal
example audit: **42/52 pass**, 10 fail, exit 100, 176.3s harness. Remaining projects
are arena, binary-tree, input-cursor, multifile-registry, owned-vector,
rbtree-augmented, refcount, ring-buffer, rust-byte-sum and rust-chunks-exact.
This is not a green archive verdict. The expensive first returned-resource
assumption has a separate preserved report at that checkpoint; the fold budget
failure itself no longer reproduces on the final indexed-order archive variant.

### Preserve the final-assumption trace context

The ordered final-assumption driver discarded each failed focused proof error
and constructed a fresh summary. Focusing also created a semantic root without
linking its existing checked trace prefix. Retain one selected failed goal's
diagnostic on the original summary and register the focused root under that
prefix. This restores recorded execution and successful `have` steps through the
existing renderer; it introduces no facts or output format.

The regression rejects a deliberately false second postcondition after a checked
store and true stored-value fact. It checks the original driver summary and the
presence of those earlier operations, and refuses any trace fact asserting the
false claim. All 135 selected current-upstream diagnostic and proof-trace controls pass
(2.47s). A freshly rebuilt CLI rejects the false claim with the original summary
and useful checked prefix. Formatting, mdBook, docs lint and whitespace checks
pass; advisory Vale is unavailable. Archive checkpoint
`e5305eeba` preserves the original false-claim and string-clear reproductions.

### Selected complete-read bridge for resource deltas

Recovery checkpoint `c72759eb7` closes a producer/checker mismatch when unfolding
a returned resource. The kernel's instantiated loadability premise and the
surface-produced fact name the same backing address through different registered
pointer reads. The existing delta index already selects a unique body premise;
only its exact named address-equality bridge was missing.

For that selected pair, admit only complete eight-byte registered reads at the
same positive pointee scale and check their recorded memory evidence. Retain the
evidence in the existing rewrite capture for rechecking. Upstream's legacy
`Bits32` pointer encoding additionally checks the raw term's eight-byte access
width before using the recorded-only equality constructor. This is numeric
loadability transport; it supplies no object designation or allocation token.
Ambiguous premise selection, changed lifetime metadata, overwritten cells,
partial writes (including the upper half), and narrow-only reads remain refused.

All 337 selected archive execution, memory, pointer-effect and native-record
controls pass. The focused unfold-and-free reduction verifies its three proofs
and passes fresh, expanded, rewritten and retained checks with a rebuilt library.
The latest normal archive audit remains **42/52**, with the same ten failures
(136.3s harness, exit 100). The original vector allocation fold still rejects its
full pointer-value comparison. This is not archive activation. Upstream
extraction passes all four targeted controls and all 707 scaling tests with two
workers (59.3s). The initial scaling run timed out one endpoint test while a
compiler ran concurrently; that case passes alone in 6.8s, and the complete
rerun passes without changing limits. Formatting, mdBook, docs lint and whitespace
checks pass; advisory Vale is unavailable. The full gate and nightly remain CI
work.

### Contained-range counterpart of the read-frame bridge

PR #1055 merged; both pushed commits `825879a46` and `61c6ae286` are verified
upstream. The same selected complete-read bridge also applies to a
`CResourceContains` body fact whose child range has another recorded pointer
name. Keep the exact parent, bounds, width and unique-source checks; only the
selected bases use the existing eight-byte frame certificate.

All four targeted controls and all 708 scaling tests pass (two workers, 52.8s
scaling harness). The containment case uses a separate pointer cell, so an
earlier loadability proof cannot warm the equality being tested. Changed
parents/bounds, ambiguous sources and an upper-half overwrite reject. Formatting,
mdBook, docs lint and whitespace checks pass; the full gate and nightly remain
CI work. No native input promise or allocation-token equivalence is broadened.

### Indexed allocation discovery before retirement

The recovery refold-and-free reduction exposed allocation discovery in `free`
materializing and scanning the whole resource context. Independently of the
archive's native pointer model, upstream can select allocation-token candidates
through the existing token-shape and pointer-root index. The final exact raw-base
check remains unchanged; this delivery does not admit new pointer aliases,
allocation identities or authority. Token consumption, full backing ownership,
live-loan checks and lifetime retirement continue through their existing checks.

The recovery native-input repair is separately preserved at `576012956`: a
uniquely indexed live witness retains its original coordinates through checked
complete-read frames. Its refold-and-return reduction verifies three proofs and
passes fresh, expanded, rewritten and retained checking; all 220 related controls
pass. The refold-and-free reduction still rejects, and the original vector and
ten-failure archive audit remain open. This delivery is a selected lookup repair,
not activation of that archive model. PR #1058's final head `19b3739ea` is verified
in upstream history.

All 46 selected heap tests pass, including the 0/16/64/256 unrelated-allocation
regression (1.74s harness). Existing double/interior-free, missing-authority,
view, loan and external-allocation controls remain green. Formatting, included
scaling-file formatting, mdBook and whitespace checks pass; advisory Vale is
unavailable. The full gate and nightly remain CI work.

### Selected stale-reference checks before reallocation

PR #1059 merged, and final pushed head `3d55c023b` is verified upstream.
The adjacent reallocation path still projected all held resource observations
and scanned all facts after consuming the old allocation and backing range.
It now uses the same conservative block-reference candidate index as free,
with the existing separation check and error for a retained dependent resource.
Resource observations are projected only when a candidate remains. This avoids
visiting unrelated allocation tokens; it does not change pointer equality,
authority, loan checks, or the semantics of reallocation's pending result.

All 47 heap controls pass (1.13s harness), including deterministic
0/16/64/256 unrelated-token scaling and rejection of the same persistent
composite view at both free and reallocation. Formatting, mdBook, structural
documentation lint and whitespace checks pass. Advisory Vale is unavailable;
the full gate and nightly were not run locally.

### Scalar field observations exclude alignment padding

PR #1062 merged; final head `7acb5544a` is verified upstream. The next
independent extraction addresses the source projector's scalar field names.
A field's physical ownership span can include alignment padding before the
next member. That span does not declare more scalar values. Name only the
retained scalar or scalar-array element count, using its actual value width
and checking that the complete observation fits inside the owned span.
Ownership extents stay as declared.

The recovery checkpoint `f53b66c39` also reconstructs the owned C input's
parametric observations and attaches read cores to its exact owner. Its 98
focused and 341 broader controls pass; the next modular application repair
is separate from this source-only scalar extraction. The last normal archive
audit remains 42/52, and no archive activation is claimed here.

All 13 focused projection controls pass, including owned/viewed scalar padding
and scalar-array counts at 0/16/64/256 sizes. All 52 normal example projects
pass (328.71s harness, concurrent recovery compilation; not a performance
comparison). Formatting, mdBook, structural documentation lint and whitespace
checks pass. Advisory Vale is unavailable; the full gate and nightly were not
run locally. The initial extraction referenced an archive-only type helper;
this delivery uses master's existing array variants.

The first CI run exposed a guarded recursive-view unfold regression. The
rewrite compared read descriptions using actual supplier merging, which correctly
refuses to merge separately bound loans. Description equivalence now checks
coverage of the existing read cores without changing any supplier or loan binding.
Owned resources and before/after loan consistency still require their existing
checks. A real-loan regression covers contiguous coverage, gaps, excess extent,
absence of ownership grants, unchanged bindings, and unrelated ranges at
0/16/64/256 sizes. All 413 selected kernel controls and all 3,979 normal Markdown
fixtures pass. Clippy with warnings denied also passes. These checks follow the
earlier 52-example run; the full gate and nightly were not run locally.

### Modular C prefix compatibility control

PR #1063 merged; both pushed commits `d0900a8ba` and `fc69c7a10` are
verified upstream. All 711 scaling tests also pass with the gate's 8 MiB Rust
test stack setting; the initial run omitted that setting and overflowed a Rust
importer test.

The next small delivery retains the unchanged vector-push C body, storage
resource and contract, with a caller that exports its prefix guarantee. The
caller uses `simp` to bridge the callee's returned read observations; exact
`assumption` alone is insufficient. Fresh verification, expansion, rewritten
verification and retained rechecking pass on current upstream. The same control
passes all four modes in recovery checkpoint `417678854`. This is a shared C
compatibility baseline, not activation of the recovery model. The archive's
grow-then-push proof and ten-failure audit remain open.

### Retain checked spellings in nested proposition proofs

PR #1070 merged; final head `2939473e5` is verified upstream. The next
independent extraction retains the source-to-kernel spelling of checked
`transport` and `instantiate` conclusions inside immutable fixed-state and
return-outcome proposition scopes. These scopes lack the frontier/outcome
carrier that already retained the spellings for outer proofs. A later rewrite
can otherwise repeat the C expression's memory reasoning.

A dedicated persistent proof-local cache carries normalized spellings, separate
from authored forms used for certificate printing. Rewrites keep authored lookup
precedence and presentation, substitute binders only for internal lookup, and
still require an available checked fact. Instantiation freezes its evaluated argument so historical
expressions cannot evaluate it at a different point. Unsupported spellings
remain optional, and new goals still lower against their actual state. No
resource, pointer-origin or object authority is introduced.

Both new deterministic controls pass at 0/16/64/256 unrelated-fact sizes;
retained lookup costs less than re-lowering. They reject a spelling without
its fact, a missing instantiation guard, and reuse after rebinding a proof name.
All 107 selected logical/expansion/index controls pass on current upstream.
The initial normal Markdown audit passed all 3,990 fixture records before
the CI correction below. The recovery return-frontier
repair is checkpointed at `3712a8fb2`; the original vector remains incomplete,
and the last archive audit remains 42/52.

CI caught a printable-certificate regression in the original augmented-tree
`compute_size_restores_subtree_size` proof. Normalized internal values had
leaked into authored source selection and rewritten goal presentation. The
lookup cache is now separate, and rewrites preserve their original written
equality when presenting the successor. A third regression pins the authored
proof-local name in that successor; the first two also pin that authored
source-index storage is unchanged. All 46 normal fixed-state recovery controls
pass with the gate stack setting (16 nightly tests skipped), and the exact
upstream sidecar that failed CI now verifies unchanged. The initial broader
recovery run omitted the gate stack setting and overflowed a deep case test;
its gate-setting rerun passes. PR #1081 merged, and both pushed commits `346b87a69` and `76b262027`
are verified upstream. After the correction, all 52 normal example projects,
46 normal fixed-state controls, and library Clippy with warnings denied pass.
The full Markdown corpus was not repeated after that correction. These are
upstream checks; the recovery archive still has ten known example failures.


## Loop resource selector closure

The selector report remained open after the complete reduced loop repair at
`53da27b58` and the shared upstream extractions. Its original C and proof are
retained in
[`loop_resource_backing_range_fold_after_write.md`](../mdtests/loop_resource_backing_range_fold_after_write.md),
with fresh, expanded, rewritten and retained checking covered by
`descriptor_backing_range_loop_survives_all_proof_modes`. The introducing
`MemberAddress` escape error belongs to archived `3e6d4cc0e7`; the carrier
repair is preserved at `6b8c5a1bb`. Upstream does not contain that archived
`MemberAddress` representation. No new object-model activation is needed to
close this selector regression.

The rejection controls preserve the authority boundary: selecting a backing
resource without a descriptor view is refused, owning an uninitialized local
descriptor does not initialize its pointer, and a loop that changes the pointer
cannot retarget the entry backing owner. These are retained in
[`loop_resource_selector_requires_descriptor_view.md`](../mdtests/loop_resource_selector_requires_descriptor_view.md),
[`loop_resource_selector_rejects_uninitialized_field.md`](../mdtests/loop_resource_selector_rejects_uninitialized_field.md)
and
[`loop_resource_selector_rejects_overwritten_field.md`](../mdtests/loop_resource_selector_rejects_overwritten_field.md).

Recovery checkpoint `7ccabaee9` rechecks the unchanged reduction in all four
proof modes through the public verification, expansion and retained-session
APIs. It passes all three new selector rejection controls, both selected
loop-argument rejection controls, all seven loop-carrier controls, all three
exit-local argument controls and all three selected actual-call/domain controls.
The original arena C is unchanged. Its project gets past the selector and now
stops at `arena_alloc.contract` tactic 239: `fold requires ownership of the complete instance body`. This later range
refold is still recovery work; closing the selector report does not restore
arena or change the last full example-audit count. No work or proof limit was
raised.

The broader archive
`c_declared_member_domains_reject_scalar_sibling_traversal` control still fails
by accepting `*(&pair->first + 1)`. This is the separately tracked
[scalar-subobject defect](../bugs/pointer-arithmetic-crosses-scalar-subobject.md),
not a passing domain check or a full green-gate verdict.

On upstream-based `b1af9a1b2`, the three new rejection fixtures and four
existing loop-exit resource argument fixtures pass. The original reduced loop
passes `click audit --claim probe.contract` at all four smart sites, including
cold and retained rewritten verification and the expansion fixed-point check.
The original arena sidecar verifies all nine selected proofs. All 42
documentation checks pass. The full and nightly gates were not repeated.


## Pointer-field postcondition closure

Recovery candidate `ebe4f69a1`, based on `80d5584ac`, restores the complete
original owned-vector project (13 proofs). The original owned-string project
also passes all 15 proofs. C, contracts, resources and work budgets are unchanged.
This supersedes the earlier partial postcondition and callee-prefix reports;
it does not activate the archived object model or update the full example count.

The remaining grow-then-push prefix proof used only grow's old-prefix equality
and tried to frame it across push's writable buffer. Instead, instantiate
push's exact guarantee at `statement(8).exit`, carry the post-call read to the
current state and the earlier read to `statement(8).entry` separately, then
rewrite the resulting element equalities. The complete repaired caller passes
`click audit --claim allocated_vector_push.contract`: all six smart sites pass
expansion, cold rewritten verification, retained checking and fixed-point checks.
No pointer identity is inferred from numeric address equality.

Full-project verification then exposed a structural branch-join regression in
`vector_replace_if`. Its arms already retain checked statement-effect counts,
including the modular call's complete-pointer refinement. Structural joins
discarded their walked memory-step records and tried to reconstruct the chain
from snapshots. Preserve the same records already used by interface joins.
Exact arm-delta, source, continuation, state and effect-coverage requirements
remain in place. The original getter, setter, conditional caller and contracts
are preserved in
[`c_pointer_field_preserving_calls_join_branches.md`](../mdtests/c_pointer_field_preserving_calls_join_branches.md).
The recovery reduction verifies all three proofs.

The recovered original string push/clear claims also pass all eight selected
audit sites. The branch reduction passes its one smart-site audit. The permanent
`owned_vector_grow_then_push_prefix_rechecks_in_all_proof_modes` regression reads
the original vector project, expands the complete caller, checks it cold, and
rechecks it in a retained session. Wrong setter results and missing backing
authority are rejection controls. A separate four-size branch control varies
unrelated caller requirements; the existing effect-delta, uncertified-effect
and memory-coverage rejection controls remain active.

On the upstream extraction, all 723 active scaling tests and the named
64/128/256/512-requirement branch scaling control pass. All 14 selected checked
execution controls pass, including wrong arm deltas, uncertified effects,
insufficient memory coverage, forged resource events and invalid source tails.
The original-vector four-mode regression and both branch rejection mutations
pass. Slow new controls run by name here and remain in nightly for the gate.
