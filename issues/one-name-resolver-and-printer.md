# One name resolver and one printer for surface syntax

Priority: P1.

Soundness: soundness-adjacent. No false acceptance is known. Surface name
resolution is part of trusted lowering: the claim the kernel checks is the one
the resolvers produced, so a name bound to the wrong declaration states a
different claim from the one the reader wrote. Today each kind of name has
its own resolver with its own shadowing and import rules, and a reviewer has
to check each one. The printers are not trusted, because expansion output is
re-checked, so a printer that spells a name wrongly makes expansion fail, not
verify a false claim.

P1 by user direction (2026-10-16).

## Progress

The first consolidation shares the parser tokenizer's byte spans with source
expansion and `ProofSourceIndex`, removes the expansion lexer and its three
raw-text name-spelling helpers, and puts library import and theorem-shadowing
policy in `src/surface/names.rs`. Source and diagnostic propositions now use
one printer with an explicit mode, including conditional-expression predicates.
Comments and literals cannot introduce bindings or have their paths rewritten.
See [Surface names and source printing](../docs/internals/source-names-and-printing.md)
for the implemented boundary and remaining migration.

Code regions now resolve through one function, `CodeRegionRef::resolve`, in
annotation lowering and proof execution. A loop label can no longer be bound
to two loops on one path. Before, `at(L.exit, ...)` read the last loop named
`L` while label regions resolved to the first
(`mdtests/a_loop_label_names_one_loop.md`). A recorded snapshot is now one
entry per program point, reached by `loop(N)` or any of the loop's labels.

Proof binders now share one rule, applied by `bind_proof_name`: the newest
binding wins wherever a name is read, and a proof binder cannot hide a C
variable in an execution proof. Before, a value binder could reuse a `have`
fact's name, so a citation read the fact while an expression read the value,
and a match-arm binder could hide a C parameter. That made
`mdtests/rb_at_rejects_wrong_color_bit.md` refuse its fold at the parent
word instead of at the color bit it tests. Step and call results follow the same
rule: a result hides an earlier proof binding of its name
(`mdtests/a_step_result_name_can_be_bound_again.md`). Contract and theorem
`let` names stay reserved.

Every lexical name the parser tracks is now in one `NameTable`: plain names
indexed by kind, and the names that carry data (resource instances, C
parameter types and objects, struct, reference and aggregate parameters, arm
binder types, facts) beside them. Cross-kind queries and shadowing are table
methods.

The parser records every braced proof block it reads, with the start of each
tactic in it. `click-verify` builds its `ProofSourceIndex` from the blocks the
entry module's verification parse recorded, instead of guessing from the
token before each brace. The guess also took resource `match` arms, `if`
expression branches in pure functions and the bodies of C functions named
`open` for proofs. Expansion reads each block's tactics from those records
too. Only the end of a one-tactic proof, `by T();`, is still found from tokens
(`tactic_end_token`), in expansion and in `ProofSourceIndex`.

Selectively imported names resolve in the parser, where it reads a Click call
or an `unfold` target, instead of in a pre-parse rewrite that guessed a
reference from the next token. A library path is still joined before parsing,
but keeps its written spelling for C and C++ declaration names. Before, a C
function, a C++ namespace member or class member, a resource binder, an enum
constructor or a tactic with a library spelling was renamed to the library
declaration
(`mdtests/a_selectively_imported_name_keeps_c_and_binder_meanings.md`,
`mdtests/a_cpp_namespace_may_share_a_library_module_name.md`,
`mdtests/a_selective_import_cannot_clash_with_a_tactic.md`).

Resource instance families are still decided twice: the parser binds a child
an `unfold` introduces under its parent's resource, and declaration expansion
repairs it from the slot, by identity, for the whole declaration. A call's
produced instance now records its resource there as an explicit fold does.
Before, a name that had held a child kept the child's resource after `step`
bound it to another instance, so `x.v` read the wrong field and a false claim
verified
(`mdtests/a_produced_instance_reusing_a_child_name_does_not_read_the_child_resource.md`).
What expansion has fixed about an instance is now kept per proof path: each
arm of an `if`, `match`, `cases`, `branch` or induction starts from the state
before the arms, and afterwards an instance the arms gave different resources
is refused where it is used
(`mdtests/one_name_may_bind_children_of_different_resources_in_two_arms.md`).
A resource's child slots and the resource each owns are one definition,
`CompositeResourceBody::child_slot_resources`, read by both the parser and
declaration expansion. The parser records a new child under its slot's
resource when the parent's arms agree on it, so an `unfold` of the child
reads the child's own fields and slots
(`mdtests/an_unfold_of_a_child_reads_the_child_resource_slots.md`). A slot
whose resource differs between the parent's arms takes the resource of the
arm an enclosing proof `match` on the parent's field selects
(`mdtests/a_proof_match_selects_the_resource_of_a_slot_its_arms_differ_on.md`).
A proof binder hides a contract value binder of its name, as it hides a fact
or a resource instance
(`mdtests/a_proof_binder_hides_a_value_binder_of_its_name.md`).

Two names that read as two declarations are refused where they are declared.
A value binder named like a C variable made `owns s.n` read the variable and
`requires s.n` the binder, and a false claim verified
(`mdtests/a_value_binder_cannot_take_a_c_variable_name.md`). An enum named
like an in-scope library module made `nat::add` the library's function rather
than the file's constructor
(`mdtests/an_enum_cannot_take_a_library_module_name.md`).

A pure `have` no longer matches a theorem requirement by spelling when the
proof has bound one of its names again: after `intro()` introduces a `y` that
hides the parameter `y`, `have y == 7` reads the introduced variable
(`mdtests/an_introduced_variable_is_not_the_parameter_it_hides.md`).
Declaration expansion follows a script's goal: an `intro()` variable, under
its written or `intro() as` name, and an `obtain` witness have their types
for constructor inference in the tactics after them
(`mdtests/a_proof_binder_has_its_type_for_constructor_inference.md`).
Constructor inference still fixes a constructor's type arguments from its own
arguments before the type its position expects, so
`function wrap(x: int32) -> List<int64> { List::Cons(x, List::Nil) }` is
refused while the explicit `List<int64>::Cons(...)` is accepted.

The kernel-term printer names a bound variable `k`, `k1`, ... and skips any
name a free source variable has, so a goal over a free `k` no longer prints
as `forall (k: int32) { k == k }`
(`mdtests/a_printed_binder_does_not_capture_a_free_name.md`).

A declaration cannot take a name the language already reads another way: a
predicate or function named like a built-in form such as `defined(...)` or
`old(...)`, whose calls read the form, and a theorem named like a law the
kernel supplies, whose citations apply the law. Before, both were accepted
and the built-in won, so claims about the declarations verified falsely
(`mdtests/a_predicate_cannot_take_a_built_in_form_name.md`,
`mdtests/a_theorem_cannot_take_a_kernel_law_name.md`). An imported user
module's declarations bind their bare names as the file's own do: an
imported theorem shadows a bare library theorem, and a selective library
import of an imported name is refused
(`mdtests/an_imported_theorem_shadows_a_bare_library_theorem.md`,
`mdtests/a_selective_import_cannot_clash_with_an_imported_declaration.md`).

The duplicate, cross-kind and reserved-name rules for top-level
declarations, which were repeated in each kind's validation loop, are one
`DeclarationTable`; each predicate, contract, function, resource and theorem
is declared there once, and validation reads its arities from it.

Source output has one printer, `print_proposition` with
`format_proof_tactics`: expansion prints a kernel fact as the Click proposition
it was lowered from, and no expansion path calls the kernel-fact printer.
`docs/internals/source-names-and-printing.md` documents that printer as the
diagnostic extension, with its own explicit modes.

The complete scoped table for parameters, fields, binders, constructors,
resources, program points and project modules remains open. Proof inventories
still interpret shared parser tokens; parser-produced AST spans and integration
of all source printers are also still required. Keep this issue until all
acceptance criteria below are met. The audit below describes the original
baseline; the separate lexer and raw-text spelling helpers it names are removed.

## Current state and violated invariant

There is no scoped symbol table for surface names. Resolution is spread by
kind of name and by phase:

- module paths are rewritten at the token level before parsing
  (`resolve_library_paths`, `src/surface/parser/library_paths.rs`), and
  projects merge modules separately (`resolve_click_project`,
  `merge_modules`, `src/surface/modules.rs`);
- parameters and fields resolve in the parser (`resolve_reference_parameter`,
  the `resolve_field_*` family in `src/surface/parser.rs`);
- binders and constructors resolve during validation (`resolve_value_binders`,
  `src/surface/validation/declaration_expansion.rs`; `resolve_constructor`,
  `resolve_call`, `resolve_comparison`,
  `src/surface/validation/constructor_inference.rs`);
- theorems and lemmas resolve in proof lowering
  (`resolve_theorem_application`, `resolve_generic_theorem_application`,
  `resolve_simp_premises`);
- resources and program points resolve in annotation lowering
  (`resolve_proof_resource_arguments`, `resolve_resource_field_schema`,
  `resolve_program_point_ref`, `resolve_code_region_ref`).

Each keeps its own map: `ContractEnvironment`, `PredicateEnvironment`,
`ClickFunctionEnvironment`, `TheoremEnvironment` (which implements its own
"a later declaration shadows an earlier one" rule), `DeclaredResourceScope`,
and the parser's quantifier-only `Scope`.

Printing back to source is also split, and the printers depend on each other
in ways that change their output:

- `source_click_proposition` and `format_proof_tactics`
  (`src/surface/printing.rs`) write `.click` text for expansion, but hand
  every case they do not handle to the diagnostic describer
  `describe_click_proposition` (`src/surface/diagnostics.rs`);
- that describer reads the thread-local `REFUSAL_SPELLING`, and in that mode
  emits sugar such as `(unsigned)` that is not source syntax, so source
  output depends on a diagnostic mode;
- kernel facts render through a third printer, `render_proposition` /
  `render_proposition_labeled` (`src/surface/proof_diagnostics/render.rs`,
  with `render/surface.rs`), with its own source, display and kernel-fallback
  modes.

Expansion does not use the parser's resolution to decide how to spell a
name. `library_citation_spelling` (`src/surface/expansion.rs`) decides
shadowing by scanning lines that start with `theorem `, and decides imports
with `selectively_imports` (which splits raw text on `;`) and
`library_module_in_scope`. It finds proof blocks with its own lexer,
`scan_source_tokens` (called 30 times in `expansion.rs`, and the base of
`ProofSourceIndex` in `expansion/source_index.rs`), which disagrees with the
parser's tokenizer (`src/surface/parser/tokenizer.rs`): it skips `#` as a
line comment, which the parser refuses, lexes `::` as two `:` tokens, and
special-cases `{closure#N}` and `(lambda#N)`.

This has already produced fixed defects of one family. Expansion printed
`bytes::equal` and `list::append_left_identity` where the file could not
resolve them (fixed in #1110). `auto` proved a `have` its expansion could not
spell. A branch prerequisite printed `<unnamed A>` and raw float bits. Each
fix added a special case to one printer.

The invariant: every surface name resolves through one scoped symbol table,
which records each use's declaration and source span. Every printer of source
text asks that table how to spell a name in a given scope, and expansion edits
the file through parser spans, not through a second lexer.

## Intended regression

Add mdtests that expand proofs whose names each printer currently spells
from text: a library theorem shadowed by a local `theorem`, a selectively
imported and a path-qualified library name in the same file, a resource and a
binder with the same spelling, and a proof block after a `/* ... */` comment
holding a `#`. Each expansion must re-verify and spell every name the way
the file resolves it. Keep the existing expansion round-trip regressions,
including `mdtests/qualified_library_names.md` and
`mdtests/memcmp_const_unsigned_char_arguments.md`.

## Acceptance criteria

- One symbol table, built once per file and project, serves parameters,
  fields, binders, constructors, theorems, resources and module paths. The
  per-kind resolvers become queries on it, and shadowing and import rules
  are written once.
- One printer writes source text, and asks the symbol table how to spell
  every name. No source output depends on a diagnostic thread-local.
  Diagnostics print through the same printer, or through a documented
  extension of it.
- `scan_source_tokens`, `library_citation_spelling`, `selectively_imports` and
  `library_module_in_scope` are removed. Expansion splices through parser
  spans.
- `docs/internals/` describes the symbol table and the printer.
- The gate, the nightly corpus and the expansion audit show no verdict
  changes. Any change that does appear is filed and explained.
