# Files and sidecars

Click specs live beside C source files. The C file contains executable code.
The `.click` file names the C file and gives contracts for functions in it.

A tiny project might look like this:

```text
increment.c
increment.click
```

The C file contains the implementation:

<!-- verified-example: mdtests/increment_requires_no_overflow.md -->
```c
int32 increment(int32 x) {
    return x + 1;
}
```

The Click sidecar names the C file and specifies the function:

<!-- verified-example: mdtests/increment_requires_no_overflow.md -->
```click
verifying "increment.c";

int32 increment(int32 x) {
    requires x < 2147483647;
    ensures increments: result == x + 1 by auto;
}
```

The function signature in the `.click` file must match the C function. The body
of the Click function is not executable C; it is the contract and proof surface
for the C function.

## The `verifying` clause

Each sidecar starts with one or more source declarations:

<!-- verified-example: mdtests/increment_requires_no_overflow.md -->
```click
verifying "increment.c";
```

This tells Click which C source files are part of the verification unit. Larger
sidecars can name multiple C files when a proof depends on helper functions.

A directory can set the C target and modeled runtime once for its sidecars in
`click.project.json`, with optional `target` and `runtime` string fields. For
example, `{"target":"x86_64-linux-userspace","runtime":"modeled-pthread"}`
selects the conditional pthread model. Existing `target` and `runtime`
directives in `.click` files remain valid when they agree with the project
config. The selected profile is bound to proof artifacts and incremental
sessions; configuration changes require a fresh verification.

## Local specification imports

A sidecar can reuse logical declarations from another local Click file:

<!-- verified-example: mdtests/specification_imports.md -->
```click
import "specification_imports_model.click";
```

Imports are relative to the importing file, transitive, and confined to the
project root. Paths are canonicalized to stable project-relative module
identities; cycles, missing files, escaping paths, and ambiguous unqualified
declarations are errors. A single-sidecar CLI input uses the sidecar's
directory as its root, widened to the nearest directory that also holds every
module the sidecar transitively imports, so a sidecar that imports a sibling
project (`../rbtree-model/rbtree_model.click`) selects their common parent,
the same root the directory form of the command uses; directory-target
verification passes its selected Click project root explicitly. This keeps
import boundaries independent of version control while permitting an
intentional project to share specifications across sibling directories.
Libraries may export algebraic types, predicates, pure functions, resources,
theorem statements, named contracts, C function specifications, and tactics.
An imported file's `verifying` declarations select sources when that file is
verified itself; they do not add translation units to the importer. The entry
file selects the C sources for its own verification, including implementations
whose imported contracts it uses.

An import provides declarations, not a request to run proofs. Verifying an
entry sidecar checks only theorem, C function, and tactic proofs owned by that
entry. It may assume imported theorem statements and the well-formed contracts
of imported functions and tactics. Imported C signatures must still match the
implementations supplied by the entry. Select a library file itself—or a
directory scope that contains it—to check the library's proofs. Circular theorem justification and
the existing checked-recursion rules are enforced independently of this
selection boundary.

## Click library imports

A Click library module is named by a `click::` path that mirrors its file
under `library/`:

<!-- verified-example: mdtests/click_library_import.md -->
```click
import click::cstr;
```

`click::cstr` is `library/cstr.click`, and `click::c::string` is
`library/c/string.click`. Importing a module twice is accepted. An unknown
module, or a path outside the `click` root such as `std::list`, is refused at
the import. A project file is always imported by a quoted path. A module's
library imports reach the files that import it, like its other declarations.

Without an import a file sees the implicit modules: `click::primitives`,
`click::nat`, `click::list` and `click::c::builtins`. Library contracts come
with the code instead of an import: when the verified C declares or calls
`memcpy`, `memcmp`, `memset` or `strlen`, through `<string.h>` or its own
prototype, the file sees `click::c::string` and the modules its contracts are
stated in, `click::bytes` and `click::cstr`
(`mdtests/a_string_function_call_brings_the_c_string_contracts.md`). Every
other module—`click::bytes` and `click::cstr` without such a call,
`click::machine_integer`, `click::integer` and `click::permutation`—must be
imported before a file names one of its declarations
(`mdtests/string_predicates_need_an_import_without_a_string_function.md`).
The C++ and Rust library contracts are generated for the calls a program
makes, so they too arrive with the code.

<!-- verified-example: mdtests/a_cited_library_theorem_is_available_after_its_import.md -->
```click
import click::machine_integer;
```

A proof that cites a theorem of a module the file does not import is refused
before any proof runs, and the message names the import to add
(`mdtests/a_cited_library_theorem_needs_its_module_import.md`).
A predicate or function of an unimported module is not visible either, so a
file may declare its own declaration with that name
(`mdtests/an_unimported_library_name_is_free_for_a_user_definition.md`).
Library theorem names stay reserved: built-in tactics such as `simp`,
`arithmetic` and loop-invariant closing apply library theorems as part of
their own reasoning, whatever the file imports. When `click expand` writes
such a step out, it also adds the import its cited theorem needs.

### Qualified library names

A library declaration also has a qualified name: its module path and its
name. A full `click::` path needs no import and brings its module, as an
import would; a module in scope, implicit or imported, is named by its last
segment:

<!-- verified-example: mdtests/qualified_library_names.md -->
```click
theorem append_nil_by_paths(xs: List<int32>) {
    ensures list::list_append(List<int32>::Nil, xs) == xs by {
        apply(click::list::list_append_left_identity(xs));
    }
}
```

A short path to a module the file does not import is refused, and the
message names the import or the full path to write
(`mdtests/a_module_path_needs_its_module_in_scope.md`). A full path whose
last segment is not a declaration of its module is refused too
(`mdtests/a_full_path_must_name_a_module_declaration.md`). Library names
still carry their module prefixes, and bare names keep working; the planned
rename to `list::append` and selective imports are tracked in
[`issues/standard-library.md`](https://github.com/clicklang/click/blob/master/issues/standard-library.md).

## Contracts are per function

Each function block in a sidecar describes one C function:

<!-- verified-example: mdtests/increment_requires_no_overflow.md -->
```click
int32 increment(int32 x) {
    requires x < 2147483647;
    ensures increments: result == x + 1 by auto;
}
```

The `requires` clauses describe what callers must provide. The `ensures`
clauses describe what the function promises when those requirements hold.

## Where examples live

There are two kinds of example material in this repository:

- `mdtests/`: small, self-contained markdown tests. These are best for focused
  proof patterns and regression tests.
- `examples/`: larger example projects with ordinary `.c` files and `.click`
  sidecars. These are best for library-shaped verification examples.

For learning Click, follow the introductory concept pages and then read the
small mdtests listed in the examples catalog. For seeing how proofs are organized at a
larger scale, read the project fixtures under `examples/`.
