# Surface names and source printing

Library name resolution lives in `src/surface/names.rs`. `FileSymbols` records
implicit and written module bindings, selective imports, local theorem names,
and explicitly qualified library references. The parser keeps this table and
uses it when lowering theorem applications; source expansion uses the same
import and shadowing policy when spelling canonical library identities.

A selective import binds the bare name. Qualified modules otherwise require
an in-scope module path or the full `click::` path. A local theorem shadows a
bare library theorem. A selective import that conflicts with a local declaration
is refused. Comments and string literals introduce no bindings. Explicitly
qualified references remain qualified in rewrites: removing one can also
remove the implicit library dependency it contributes to a retained session.

The parser tokenizer supplies exact byte spans through `source_tokens`.
Expansion and `ProofSourceIndex` use these tokens; there is no expansion
lexer. Path separators, arrows, suffixed literals, closure names, lambda names,
comments and lexical refusals therefore have the parser's boundaries. The
proof source adapter inserts only zero-width braces around an implicit
single-tactic `by` body. The splicer materializes those braces when a rewrite
needs several tactics and preserves source outside its selected byte span.
Proof-block and declaration inventories still interpret the token structure;
they are not yet parser-produced AST spans.

`printing::print_proposition` is the common Surface proposition printer.
Callers select source, ordinary diagnostic, or refusal spelling explicitly. Source output always
selects source spelling, including propositions nested in conditional
expressions. A diagnostic's thread-local refusal preference cannot introduce
presentation-only `(unsigned)` text into generated source. Expression, place
and snapshot formatters are shared with diagnostics; those formatters preserve
source syntax rather than inheriting refusal mode.

Canonical library names in a generated fragment are rewritten only at parser
token spans. A matching string or comment is left untouched. Name queries read
indexes rather than scanning the original source; a source rewrite constructs
its file bindings once before spelling the fragment.

A written code region resolves through `CodeRegionRef::resolve`, both in
annotation lowering and in proof execution. A loop label binds once per
execution path, through the structural clause of the `loop as label` that
declared it; a second `loop as label` at another loop is refused. Recorded
snapshots are still stored under each spelling of their program point,
`loop(N)` and each label of that loop, and read back by spelling, so expansion
can cite the label the proof wrote.

This is the first consolidation boundary for
[`one-name-resolver-and-printer.md`](https://github.com/clicklang/click/blob/master/issues/one-name-resolver-and-printer.md),
not completion of that issue. Parameters, fields, lexical binders,
constructors, resources and program points still have separate resolution
contexts. Unifying them into one scoped declaration/use table, retaining it
across project modules, making every source printer use it, and replacing
token-derived proof inventories with parser-produced spans remain open.
