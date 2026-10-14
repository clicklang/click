# The Click library

The Click library is one Click module per file in this directory. Every
module is currently loaded implicitly with every sidecar and C-free theorem
file, in this order:

| Module | Contents |
| --- | --- |
| `primitives.click` | Verifier primitives: the abstract resources the kernel interprets (`mutex_guard`, `mutex_live`, `mutex_use`, `publisher`, `subscriber`, `authority`, `allocation`) |
| `nat.click` | `Nat`, `to_nat`, `nat_add` and their laws |
| `list.click` | `List<T>`, `list_append`, `list_contains`, `list_length` and their laws |
| `machine_integer.click` | Order, increment and definedness lemmas over native integer widths |
| `permutation.click` | `count` and `permutation` over `int32[]` |
| `bytes.click` | Byte-range predicates over `uint8[]` |
| `cstr.click` | C-string predicates and theorems |
| `c/builtins.click` | `__click_constant_p_unknown`, the value of `__builtin_constant_p` |
| `c/string.click` | `memcpy`, `memcmp`, `memset` and `strlen` contracts |
| `integer.click` | `to_integer` bridges for native arithmetic, and `Integer` division laws |

Each module is parsed with the declarations of the modules before it, and
its diagnostics name its own file and line. Types, pure functions, and
theorems use ordinary Click declarations; library theorems are checked, not
trusted axioms. The `extern` contracts are assumptions, listed in
[trust](../docs/concepts/trust.md).

A module is named by a `click::` path that mirrors its file:
`import click::cstr;` is `cstr.click` and `import click::c::string;` is
`c/string.click`. While every module is implicit, an import only checks that
its module exists. Which modules stay implicit is recorded in
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
  its entry to `docs/reference/inventory.toml`. The documentation gate checks
  these against the source.
- Run a focused fixture check, then the full `scripts/check.sh` gate. Add
  expansion coverage when exercising a new proof path.

Generic proofs are verified for each concrete instance when used. Exercise
different element families explicitly; a test at `int32` does not check every
possible instantiation. The list fixtures cover scalar and pointer elements
and append over nested lists. The library reference documents current limits.
