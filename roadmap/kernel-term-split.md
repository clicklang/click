# KernelTerm / SurfaceTerm: finish the representation split

Priority: P1.

Soundness: incomplete. Native expression bridges can preserve proof rules that
the common representation does not yet handle directly. Removing a bridge
before its callers move can lose proofs or prevent checked expansion.

P1 by maintainer direction (2026-11-24): recurring verifier bugs keep tracing
back to the unfinished split.

## Goal

`SurfaceTerm` represents source expressions. `KernelTerm` is the typed,
immutable expression DAG for supported kernel expressions. Use one
representation for expression children throughout evaluation, storage, checking,
rewriting and raising. Typed views and explicit API adapters can remain.
Memory state, resource, allocation and execution-event identities may remain
opaque semantic payloads.

The two types, the major producer and storage handoffs, and the common raising
and certificate boundaries are in place. Every shared Integer retains one
typed kernel root. Affine checking, fold comparison keys and scoped resource
substitution read retained Integer children. Opaque machine inputs retain
their written operand or observation handle in typed nodes. A call with
an opaque input retains the exact producer's argument slot. Selected readers
still use native views of these operands. Completed slices and their
validation are in the [migration history][history].

## Closure checklist

| Remaining boundary | Live callers | Close when |
| --- | --- | --- |
| Native expression inputs | [Typed scalar inputs][kernel-term] retain their exact carrier and original expression or producer slot. Opaque C value records and descriptors that the structural importer refuses remain explicit native inputs. Semantic argument observations borrow those inputs. | Complete. The generic expression payload and its Integer and algebraic readers are gone. Fold dependencies and variable collection distinguish typed scalar inputs from opaque call descriptors. |
| Pointer and address expression children | [Retained contract displacements][offsets] retain opaque indices through their exact carrier handles. Numeric observations of pointer and array arguments use typed pointer keys. Exact replacement and machine variable substitution traverse retained contract displacements. Scope and fold queries read the same displacement children. Rendering, hashing and ordinary native address descriptors still have native readers. Ownership, aliasing and read-over-write checking consume native address descriptors. | Keep the original index identities, widths, complete pointer metadata and program points. Move expression children and their readers to common operands. Keep address and state descriptors where they represent semantic identity. |
| Stored values, calls and proposition operands | [Stored values][descriptor-values], [resource fields][resource-fields] and [certification][contract-claims] still expose native output views or exact inputs. Stored algebraic constructors, pointer values, and pairs of retained floating-point arithmetic nodes compare through retained keys. Constant quantity and range-bound checks read retained machine operands. Other native equality, hashing, diagnostics and selected checker paths use the retained argument and machine caches. | Move live internal expression consumers and delete obsolete caches. Preserve fact and certificate identity, exact argument spellings, and supported refusal behavior. |
| Final common boundary | [Surface raising][raising] reads retained Boolean calls, connectives, and stored algebraic equality operands directly. Algebraic constructors use the common renderer for typed fields and literals. Certificate completion classifies retained Boolean conditions without constructing their native connective tree. Selected comparison operands and other family-specific naming and rewrite adapters remain. | Check that supported term operands round-trip through the common representation. Keep introducing names and typed frontend ASTs. Retire duplicate expression conversion paths, then remove this roadmap item after validation. |

## Delivery sequence

1. Completed. Move Integer checking and rewriting to retained operands and
   delete the paired storage and reverse link.
2. Completed. Retire generic native expression payloads and give exact scalar
   call arguments typed views of their producer slots.
3. In progress. Move the remaining pointer, address, and stored-value
   expression readers.
4. Close the raising and certificate boundaries, validate, and remove this
   item.

Recent slices: 81794d9a deletes the unused native Boolean payload adapter,
ab99c280 keeps explicitly written machine inputs in typed nodes, and
edaf815f exercises retained Integer readers with equivalent cache state;
later merges retain fold, stored-value and machine-quantity readers.

## Validation for closure

A rewritten algebraic equality can retain a match on a known constructor.
Lowering its Surface spelling may select the arm and lose the written match.
The `selected_both_sides` claim in [the bound-guards fixture][bound-guards]
exhibits this round-trip gap.

- Check exact term round trips, successful and refused proofs, checked expansion
  and replay, binder scope, historical read identities and branch isolation.
- Measure related DAG growth and unrelated context growth in deterministic work
  units. A common-operand route must avoid repeated whole-tree export.
- Pass the integration gate and the regular-corpus fact-stability audit with
  zero differences. Record the separate raise/lower census. The broader
  [raise/lower principle][principle] tracks fact and goal spelling independently.
  A census miss blocks this migration when it reproduces a break in term
  representation, round-trip identity, rule parity or scaling.

[history]: https://github.com/clicklang/click/blob/01280f00541085d1129282201892f93c306dfe70/roadmap/raise-lower-principle.md
[kernel-term]: ../src/kernel/primitives/kernel_term.rs
[offsets]: ../src/kernel/primitives/kernel_term/offsets.rs
[descriptor-values]: ../src/kernel/primitives/descriptor_values.rs
[resource-fields]: ../src/kernel/primitives/resource_fields.rs
[contract-claims]: ../src/kernel/api/contract_certification/contract_claims.rs
[raising]: ../src/surface/proof/surface_synthesis.rs
[principle]: ../docs/internals/raise-lower-principle.md
[bound-guards]: ../mdtests/algebraic_match_bound_guards.md
