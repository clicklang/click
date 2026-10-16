# Pointer bounds through integer representations

Status: the policy below was accepted in the task conversation on 2026-10-15.
The first implementation under test uses a hidden record for unchanged
complete C integers. On 2026-10-16 the user also approved cast-based contracts
for full packed-pointer relationships, using existing syntax such as
`requires ((struct node*)(word & ~1)) == p;`. Their implementation and checked
tagged-word transport are in progress. No new `represents` predicate is approved.
This extends [pointer subobject extents](pointer-subobject-extents.md)
and does not close its tracked bug.

## Accepted policy

A lossless pointer-to-integer-to-pointer round trip preserves the original
pointer's allocation origin and selected extent. Equality of integer addresses
alone never supplies either. Keep ordinary integer equality numeric. Keep the
separately approved character/void cast behavior; integer casts do not acquire
that widening rule.

C11 leaves integer-to-pointer conversion implementation-defined. This is
Click's conservative LP64 verification policy, not a claim that C specifies
one universal provenance model.

## Minimal implementation being tested

`CValue::PointerInteger` separates an ordinary signed or unsigned LP64 numeric
value from its original complete pointer. Direct casts back recover that
pointer and its selected extent. Assignment, complete stores/reloads and
whole-value copies retain the record. Changes of integer format and ordinary arithmetic discard it. Checked low-bit
tag operations retain the source pointer; the tag must be cleared before the
value is used as a pointer. Numerical equality never supplies a missing record.
Integer observations in specifications project only the number, so model
functions and numeric resource parameters cannot transport pointer authority.

An untracked nonzero integer with a checked address form can still reconstruct
that address for C comparisons, but receives a fresh opaque designation from
the execution's bounded identity allocator and no original bounds. This identity
is never interned by integer bits or merged by numeric congruence. An incoming parameter, modular result or complete typed word read now carries
its own opaque identity. An explicit specification cast names its reconstructed
pointer, so a contract can constrain that identity without first proving a
numeric address equation. Numeric expressions and model integer fields have
no such carrier. The alternative predicate below remains an unapproved design
note, not an API.

## Unpublished prototype checkpoint

At the 2026-10-16 build-75 checkpoint, all 5,526 ordinary library tests
pass, including all 733 ordinary scaling tests. All 4,049 ordinary Markdown
fixtures pass. This includes the original tagged-pointer fixtures and ten new
cast-contract cases covering copies, calls, stores, snapshots, loops, partial
writes, arithmetic invalidation and member bounds. Clippy passes with warnings
denied. The basic incoming-word, selected-member and modular-call proofs expand
and verify independently. Existing branch/mark, nested-field, packed numeric
witness and loop-exit expansion checks passed at the earlier build-58 checkpoint;
they must be rerun after the final compatibility changes.

Cached scalar observations now have a no-write memory edge, with the observed
value computed inside the kernel. Complete pointer bounds track eight bytes,
including both halves of a cached pointer. A producer-retained unchanged-byte
source lets new observations skip prior cache entries directly; the regression
measures 16, 64, 256 and 1,024 observations. Real upper-half overwrites still
invalidate the old bounds. The broader experiment that also replaced numeric
pointer coordinates with native eight-byte read nodes was withdrawn after its
compatibility regressions; numeric pointer coordinates retain their existing
representation.

After integrating upstream through `3e3f5ccd4`, the build-94 ordinary
non-scaling library run passes all 4,853 selected tests. It includes a reduced
complete-pointer read regression: a cached four-byte scalar prefix may recover
only a complete stored eight-byte pointer; an upper-half overwrite invalidates
that recovery. Numeric wide-read observations project a retained integer
record's bits without copying its pointer authority.

Complete-pointer comparisons also recover one actual whole-pointer store when
an untouched opaque read denotes a value copied from another cell. They do not
recursively chase stored records, recover from a stopped walk's scalar-prefix
cache, or undo explicit byte/void views and member selection. A focused
regression covers two cells, an intervening separated write, partial overwrite,
numeric-only stores and changed views. Its scaling test uses 16, 64, 256 and
1,024 unrelated numeric classes; all 755 scaling tests pass at build 111.

At build 89, all ordinary Markdown fixtures, all 51 ordinary example projects,
and all 754 scaling tests passed, and Clippy passed with warnings denied.
That checkpoint used character-to-character casts that preserve their incoming
bounds. One existing library policy test expects an authored signedness cast
to widen instead. On 2026-10-16 the user approved retaining bounds across
character-pointer signedness changes. The implementation and policy test now
reflect that refinement, and all 48 C-string fixtures pass. The build-99
library run passes all 5,607 ordinary tests, including all 754 scaling tests.
The build-101 full ordinary Markdown run passes all 4,169 fixtures and the
ordinary example run passes all 51 projects. With stored-value comparison
recovery, build 111 passes all 4,854 ordinary non-scaling library tests, all
755 scaling tests, all 4,171 ordinary Markdown fixtures, and all 51 ordinary
example projects. The named packed-cast fresh/expanded/retained test passes,
and eight independent expansions verify again at build 113. Clippy passes
with warnings denied. These runs include the complete read producer fix and
the approved character-pointer cast policy. The resource
semantics version is 71 to invalidate retained artifacts from the earlier
byte-cast policy.

The earlier arena, vector and Rust integer compatibility failures are resolved.
Eight independent expansion/verification checks and the named packed-cast
fresh/expanded/retained test passed after the first upstream integration.
They need rerunning after the final compatibility changes.

The affected named `rbtree-erase` nightly project is under investigation.
Its packed-parent resources need the approved full cast relationships in
addition to numeric address facts. A scratch proof with those relationships
gets farther, but its complete left-child read across the transplant still
fails; this is not counted as fixed. The equality holds before the transplant.
An explicit frame transport and an explicit separation of the intervening
parent-word store from the child field do not close the later obligation.
Smaller model-alias and packed-cast/store/call probes pass, so the general
cause is not established. The investigation and resource adaptations remain
in a scratch copy; the existing tree proof has not been weakened.

After the complete-read producer fix, all 754 scaling tests and the named
packed-cast fresh/expanded/retained test pass again. Clippy passes with warnings
denied. The authored `void*` identity-cast control also passes: every explicit
cast to `void*` still widens, including when its operand already has that type.
No C implementation source was changed, no full nightly suite was run, and no
PR has been published.

The hidden-record experiment closes the direct integer escape; it does not
complete Phase B or justify closing the parent bug.

## Reproduced escape

`mdtests/a_pointer_integer_round_trip_keeps_its_subobject.md` converts
`&pair->first` to `unsigned long`, casts back, and reads element one. The
upstream implementation accepts this undefined dereference. The ordinary
mdtest expects rejection and now passes in the working prototype. Keep the original C and both
field permissions in the regression.

The existing `PointerAddress(Box<Pointer>)` records only a physical address.
`cast_tagged_address_to_pointer` can also recover that address from a numeric
word equality. Reconstructing `CPointerValue::new` then loses the selected
extent. Merely putting the full pointer in that term is insufficient: numeric
rewrites, pure-function congruence and resource argument matching could copy
its bounds to another equal integer.

## Approved cast-based contracts

Use existing full pointer equality, without adding a predicate:

```click
requires ((int32*)word) == p;
```

Under Phase B this states designation equality as well as address equality.
A tagged word can use the corresponding masked cast. Evaluation must be able
to name an opaque reconstructed pointer before its origin is established;
otherwise this spelling would circularly require the relation it is declaring.
Numeric rewriting of the word must not rewrite that opaque origin. The frontend and evaluator now support this spelling. Ordinary tests cover
incoming words, local copies, whole stores/reloads, partial overwrites, saved
historical values, selected scalar bounds, and explicit modular postconditions.
The basic incoming-word, member-read and modular-call claims also expand and
verify independently. Recursive resource witnesses use the same cast equality;
the original marked-list project now verifies without C changes. The loop case and numeric-observer compatibility checks now pass the ordinary
suite. The wider Phase B example compatibility work remains open.

Logical caches retain numeric observations. Complete reads construct their
opaque word identity from the actual eight-byte source, so caching does not
change physical memory or create a stored pointer representation. A logical
cast names that value independently of its own assumed relationship; execution
may then adopt bounds from full-pointer premises and choose numeric coordinates
from ordinary address equations. These are separate operations.

The latest scoped full-pointer premise retains its predecessor equality graph.
Withdrawal uses exact persistent fact-map roots to restore that predecessor
without rebuilding unrelated classes. Interleaved withdrawals continue through
the existing rebuild path; this optimization does not make all graph deletion
constant-time.

A distinct representation-bearing word type is another alternative. It makes
full-value transport explicit but changes substantially more model and contract
interfaces. Ordinary mathematical integer values and equality must remain
numeric whichever spelling is chosen.

The explicit predicate below is an alternative proposal, not an approved API.
It was initially recommended for clarity around packed/tagged words; existing
cast equality is preferable if it can express and transport the same relation.

## Alternative explicit predicate

Add `represents(word, pointer, tag)`, stating both:

- `word` numerically equals `address(pointer) + tag` under the checked tag rules;
- the complete C word carries `pointer`'s origin and selected extent.

The first operand denotes a complete C parameter, result, or scalar load,
including an `old`/`at` observation of one. A mathematical integer expression
alone has no representation carrier. The pointer operand is a complete pointer
value. The tag operand is numeric. Proving only the first bullet cannot prove
the predicate.

For a tagged parent field, the model would use:

```click
let parent: struct rb_node* where aligned(parent, 8) and
    represents(node->__rb_parent_color, parent, node->__rb_parent_color & 1);
```

For a modular word copy, its contract must preserve `represents` when callers
need to reconstruct a pointer with usable bounds. A numeric postcondition
`result == word` still establishes only its mathematical meaning. Existing
C and its claims stay intact; resource/proof contracts receive the explicit
representation relation where their intent already depends on it.

## Representation and proof boundary

Keep each complete C integer's bits and representation carrier separate.
The carrier is a complete source pointer or an opaque incoming/loaded word
identity. It is not an address-indexed registry, and numeric classes never
choose a carrier. Copying, binding and complete stores/loads transport it.
Partial writes invalidate it; supported complete representation copies retain
it. New allocation producers establish their own known allocation extent.

Arithmetic changes the numeric component. Preserve a pointer carrier only
through the checked lossless tag operations; a zero-tag cast back returns the
same pointer designation. If an operation loses the carrier, an address may
still be recoverable for comparisons, but dereference requires an explicit
representation relation. Do not reconstruct a known allocation extent merely
because the recovered physical block happens to be concrete.

Numeric equality rewrites change numeric components and leave existing
carrier identities intact. Lexical substitution of actual C values transports
both components. Specification integer functions and ordinary integer model
fields remain mathematical: their numeric congruence does not transport a C
representation carrier. A resource that needs one names the actual C word
observation and the pointer model, rather than inferring it from an ordinary
integer argument.

The cast relationship uses its own full-value origin index, with
exact support and scoped withdrawal, independently of the numeric equality
graph. Reading through equal storage addresses may identify a complete word
read; equating the loaded numbers may not. Carry producer-issued full-value
facts through calls, snapshots and proof expansion. Never re-walk or validate
a producer's output in the same session.

## Required controls

| Case | Result |
| --- | --- |
| Member pointer to word and back, reading the member | Accept |
| Same round trip, reading its sibling | Reject |
| One-past member pointer round trip without dereference | Accept |
| Whole word local copy, store/reload, aggregate copy | Retain designation |
| Tag then clear supported low bits | Retain designation |
| Equal numeric addresses with different selected extents | No bounds transfer |
| Numeric equality rewrite, pure function or integer model argument | No bounds transfer |
| Entry word constrained only by its numeric address | No dereference authority |
| Entry word constrained by full cast equality | Adopt the stated designation |
| Callee returns a word with only numeric equality | No bounds transfer |
| Callee explicitly preserves full cast equality | Retain designation |
| Partial overwrite followed by reconstruction | No retained carrier |
| Withdrawal of the only representation premise | Revoke its bounds relation |

Run these in fresh, expanded, rewritten and retained checking. Add deterministic
multi-size tests for selected word-origin lookup and withdrawal beside unrelated
words, facts and memory ranges. Run all ordinary scaling tests and affected
pointer-tag/rbtree fixtures. Do not close the parent bug until integer transport
and the remaining Phase B gates pass.
