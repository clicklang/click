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
