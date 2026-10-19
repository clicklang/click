# Surface names and source printing

Library name resolution lives in `src/surface/names.rs`. `FileSymbols` records
implicit and written module bindings, selective imports, local theorem names,
and explicitly qualified library references. The parser keeps this table and
uses it when lowering theorem applications; source expansion uses the same
import and shadowing policy when spelling canonical library identities.

A selective import binds the bare name. Qualified modules otherwise require
an in-scope module path or the full `click::` path. A local theorem shadows a
bare library theorem. A selective import that conflicts with a local declaration
(a theorem, function, predicate, resource, enum or tactic) is refused. Comments
and string literals introduce no bindings. Explicitly qualified references
remain qualified in rewrites: removing one can also remove the implicit library
dependency it contributes to a retained session.

Only a Click reference reads these bindings. The parser resolves a selectively
imported name where it reads a call (`parse_call_arguments`, through
`expect_reference_name`) or an `unfold` target. A C function, a C++ member, a
resource binder or an enum constructor of the same spelling keeps its own
meaning. A library path is joined into the declaration it names before
parsing, so the parser's lookahead sees one name, and `FileSymbols` keeps the
written spelling by source position. A C or C++ declaration name, such as the
head `int list::append(int x)` of a namespace member, reads the written
spelling back (`expect_c_declaration_ident`). A path through a library module
the file does not import is refused only where a Click reference reads it.

The parser tokenizer supplies exact byte spans through `source_tokens`.
Expansion and `ProofSourceIndex` use these tokens; there is no expansion
lexer. Path separators, arrows, suffixed literals, closure names, lambda names,
comments and lexical refusals therefore have the parser's boundaries. The
parser records each one-tactic proof it reads without braces, `by T(args);`
(`ImplicitProofSpan`: the tactic's first and last token), in the file's
`SourceSpans` and in the `DeclarationBody` of the theorem or function that
holds it. The proof source adapter inserts zero-width braces around exactly
those tactics, so a certificate's `scale 1 by 2 => ...` is never taken for a
proof. The splicer materializes those braces when a rewrite
needs several tactics and preserves source outside its selected byte span.
The parser records each braced proof block it reads (`ProofBlockSpan`: its
braces and the start of each tactic), and `ProofSourceIndex::for_project`
indexes exactly the blocks the entry module's verification parse recorded.
A tactic's extent within a block is the range from its recorded start to
the next one's, so expansion finds no tactic's end by scanning tokens.

`printing::print_proposition` is the common Surface proposition printer.
Callers select source, ordinary diagnostic, or refusal spelling explicitly. Source output always
selects source spelling, including propositions nested in conditional
expressions. A diagnostic's thread-local refusal preference cannot introduce
presentation-only `(unsigned)` text into generated source. Expression, place
and snapshot formatters are shared with diagnostics; those formatters preserve
source syntax rather than inheriting refusal mode.

Source text has one printer. Expansion writes a proposition through
`print_proposition` and a tactic through `format_proof_tactics`; a kernel fact
it writes as source is looked up as the Click proposition it was lowered
from (`SurfacePropositionMap::surface`) and printed there. The kernel-fact printer,
`render_proposition` (`proof_diagnostics/render.rs` with `render/surface.rs`),
is the diagnostic extension of it, for facts a person reads in a refusal or a
`--trace-proof` trace. It prints a kernel `Proposition` directly, so it can
show what a Click proposition cannot: a read's width, snapshot and address,
report-local snapshot labels, and the kernel spelling of a fact with no Click
form. Its modes are explicit (`Mode::Source`, `Exact`, `ExactIdentity`), and
no expansion path calls it, so its output never reaches generated source.

Predicate diagnostics retain each array argument's memory snapshot. An array
read at entry prints as `old(src)`, a recorded state as `at(copied, src)`, and
the current state as `src`. Only the predicate's implicit logical resource
state is omitted; two array arguments with different snapshots remain distinct.

Canonical library names in a generated fragment are rewritten only at parser
token spans. A matching string or comment is left untouched. Name queries read
indexes rather than scanning the original source; a source rewrite constructs
its file bindings once before spelling the fragment.

A written code region resolves through `CodeRegionRef::resolve`, both in
annotation lowering and in proof execution. A loop label binds once per
execution path, through the structural clause of the `loop as label` that
declared it; a second `loop as label` at another loop is refused. A recorded
snapshot is one entry per program point. The snapshot map keeps the labels the
path gave its loops, files a loop's snapshot under its first label, and reads
`loop(N)`, that label and any other label of the loop as the same entry, so
expansion still cites the label the proof wrote.

Proof binders in the parser go through `bind_proof_name`. The newest binding
of a name wins in every reading position: a value binder hides a `have` fact
and a resource instance of the same spelling until its block ends, a
resource binder hides a fact, and any proof binder hides a contract value
binder, so `s.n` reads the newer `s`. A `forall` or `exists` variable hides the same
bindings and the bare field of an enclosing resource body until its body
ends; unlike a proof binder it may also hide a C variable. The hidden bindings are restored from the same
log as fact names. In an execution proof, a proof binder may not take a C
parameter's or C object's name; `intro()` binders keep their `outer.`
shadowing. A step or call result is stored in the proof's local values by
name, so a later result of the same name replaces it there; only a C local or
parameter of that name is refused. Every lexical name the parser tracks is in one `NameTable`
(`src/surface/parser/name_table.rs`): plain names indexed by `NameKind`
(proof binders, contract bindings, Integer parameters and lets, theorem,
reference, struct-array, `void*` and type parameters) and the names that
carry data (resource instances, C parameter types and objects, struct and
aggregate parameters, arm binder types, facts). Cross-kind questions,
`is_bound` and `is_c_variable`, and the hiding and restoring of bindings are
methods of the table. The table keeps one undo log: a quantifier, proof
block, `else` block, match arm or execution `ensures` takes a `NameScope`
mark, binds and hides through the table, and ends the mark, which puts back
everything changed since, newest first, without copying the surrounding
names.

Lexical bindings after parsing go through `ScopedNames`
(`src/surface/scoped_names.rs`): a binding hides an earlier binding of its
name until its scope ends, and ending the scope undoes, newest first,
everything bound or hidden since its `Scope` mark. An inner scope copies
nothing of the scopes around it. Constructor inference's binder types and
the return-type check's local types are `ScopedNames`.

Top-level declarations go through one declaration table,
`DeclarationTable` (`src/surface/validation/declaration_table.rs`).
`validate_click_definitions` declares each predicate, contract, function,
resource and theorem of the file and its library there, in that order, and
`declare` is the only place that decides whether a name may be declared:
it refuses a second declaration of a name, as the same kind or another, and a
name the language reserves for the kind (`same_object` and `held` for
propositions, Integer conversions for functions, `read` and `write` for
resources, kernel laws for theorems, built-in forms such as `old(...)` for
anything called). Validation reads each kind's arities from the table.

This is the first consolidation boundary for
[`one-name-resolver-and-printer.md`](https://github.com/clicklang/click/blob/master/issues/one-name-resolver-and-printer.md),
not completion of that issue. Parameters, fields, lexical binders,
constructors, resources and program points still have separate resolution
contexts. Unifying them into one scoped declaration/use table, retaining it
across project modules, making every source printer use it, and replacing
token-derived proof inventories with parser-produced spans remain open.
