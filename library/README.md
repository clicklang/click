# The Click library

The Click library is one Click module per file in this directory, listed
here in library order. A file sees the implicit modules, the modules it
imports with `import click::...;`, and the modules those import:

| Module | Seen | Contents |
| --- | --- | --- |
| `primitives.click` | implicit | Verifier primitives: the abstract resources the kernel interprets (`mutex_guard`, `mutex_live`, `mutex_use`, `publisher`, `subscriber`, `authority`, `allocation`) |
| `nat.click` | implicit | `Nat`, `to_nat`, `nat::add` and their laws |
| `list.click` | implicit | `List<T>`, `list::append`, `list::contains`, `list::length` and their laws |
| `machine_integer.click` | `import click::machine_integer;` | Order, increment and definedness lemmas over native integer widths |
| `permutation.click` | `import click::permutation;` | `permutation::count` and `permutation::permutation` over `int32[]` |
| `bytes.click` | `import click::bytes;`, or with `c/string` | `bytes::count`, `bytes::equal` and the other byte-range predicates over `uint8[]` |
| `cstr.click` | `import click::cstr;`, or with `c/string` | C-string predicates and theorems, and the borrowed-string resource `cstr_at` |
| `c/builtins.click` | implicit | `__click_constant_p_unknown`, the value of `__builtin_constant_p` |
| `c/string.click` | when the C declares or calls one of its functions | `memcpy`, `memcmp`, `memset` and `strlen` contracts |
| `integer.click` | `import click::integer;` | `to_integer` bridges for native arithmetic, and `Integer` division laws |

The implicit set is `IMPLICIT_LIBRARY_MODULES` in
`src/surface/validation/declaration_expansion.rs`. The C front end records
the modules a program's declarations and calls bring
(`library_contract_module` in `src/languages/c/syntax.rs`). A module lists the earlier
modules its declarations use with its own `import click::...;` lines.
Built-in tactics apply library theorems whatever a file imports; a library
theorem's verifier identity is its qualified name, `click::module::name`,
so a file theorem may share its bare name (`library_theorem_identity` in
`src/surface/parser.rs`). Imports gate the declarations a file names. A
library module's own proofs are checked against the whole library.

Each module is parsed with the declarations of the modules before it, and
its diagnostics name its own file and line. Types, pure functions, and
theorems use ordinary Click declarations; library theorems are checked, not
trusted axioms. The `extern` contracts are assumptions, listed in
[trust](../docs/concepts/trust.md).

A module is named by a `click::` path that mirrors its file:
`import click::cstr;` is `cstr.click` and `import click::c::string;` is
`c/string.click`. A declaration's qualified name adds its own name:
`click::cstr::len`, or `cstr::len` once the module is in scope
(`src/surface/parser/library_paths.rs`). The remaining design steps are recorded in
[`issues/standard-library.md`](../issues/standard-library.md).

The library is checked on its own, like any dependency: `verify_standard_library`
proves every library theorem, and the gate runs it in
`standard_library_theorems_are_proved_by_their_own_entry_point`. Verifying a
sidecar applies library theorems as dependency declarations and proves only
the sidecar's own theorems. Whole-contract certification accepts a pure theorem
only with kernel authority from a checked proof, so a C proof that cites one of
the few library theorems that certification consumes checks that cited theorem
once during its verification.

For a library addition:

- Add the declaration to the module for its topic. A new module needs an
  entry in `CLICK_LIBRARY_MODULES` in `src/surface.rs`, after every module it
  uses.
- Put positive and negative client examples in `mdtests/`. List clients live
  in `stdlib_list*.md` and should use the implicit library, not redeclare it.
- Add a checked use to `mdtests/stdlib_every_symbol.md`.
- Copy the exact declaration into `docs/reference/library/index.md` and add
  its entry to `docs/reference/inventory.toml`. A module in
  `QUALIFIED_MODULES` lists its functions, predicates and theorems by
  in-scope path, `library.function.bytes::count`. The documentation gate checks
  these against the source.
- Run a focused fixture check, then the full `scripts/check.sh` gate. Add
  expansion coverage when exercising a new proof path.

Generic proofs are verified for each concrete instance when used. Exercise
different element families explicitly; a test at `int32` does not check every
possible instantiation. The list fixtures cover scalar and pointer elements
and append over nested lists. The library reference documents current limits.
