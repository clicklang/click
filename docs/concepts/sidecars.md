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
Built-in tactics such as `simp`, `arithmetic` and loop-invariant closing
apply library theorems as part of their own reasoning, whatever the file
imports. They name a library theorem by its qualified identity, such as
`click::machine_integer::uint32_less_than_transitive`, so a file may declare
a theorem with a library theorem's bare name: a bare citation then names the
file's theorem, a path names the library's, and the tactics keep the
library's (`mdtests/a_file_theorem_may_share_a_library_theorem_name.md`).
When `click expand` writes such a step out, it spells the theorem by its bare
name and adds the import it needs, or by its full path when the file declares
a theorem of that name. Diagnostics name a library theorem by its qualified
identity.

### Qualified library names

A library declaration also has a qualified name: its module path and its
name. A full `click::` path needs no import and brings its module, as an
import would; a module in scope, implicit or imported, is named by its last
segment:

<!-- verified-example: mdtests/qualified_library_names.md -->
```click
theorem append_nil_by_paths(xs: List<int32>) {
    ensures list::append(List<int32>::Nil, xs) == xs by {
        apply(click::list::append_left_identity(xs));
    }
}
```

A short path to a module the file does not import is refused, and the
message names the import or the full path to write
(`mdtests/a_module_path_needs_its_module_in_scope.md`). A full path whose
last segment is not a declaration of its module is refused too
(`mdtests/a_full_path_must_name_a_module_declaration.md`).

A selective import brings bare names into scope:

<!-- verified-example: mdtests/a_selective_import_brings_bare_library_names.md -->
```click
import click::list::{append, length};

theorem append_nil_by_bare_names(xs: List<int32>) {
    ensures append(List<int32>::Nil, xs) == xs by {
        apply(list::append_left_identity(xs));
    }
}
```

Without a path or a selective import, a function, predicate or theorem of
`click::nat`, `click::list` or `click::bytes` is not in scope by its bare
name, even when the module is implicit
(`mdtests/a_bare_library_name_needs_a_path_or_selective_import.md`,
`mdtests/a_bare_list_theorem_citation_needs_a_path_or_selective_import.md`).
`import click::bytes;` puts the module in scope, so a sidecar writes
`bytes::equal`
(`mdtests/a_bytes_import_puts_the_module_not_its_names_in_scope.md`). A C
string call brings the `bytes` contracts but not the module name, so a
sidecar without the import writes the full path, `click::bytes::all_equal`
(`mdtests/a_string_function_call_brings_the_c_string_contracts.md`).
A file may therefore declare its own `append`
(`mdtests/a_file_may_declare_a_library_function_name.md`). A selectively
imported name that a file also declares, or that two selective imports
bring, is refused, as Rust refuses a clashing `use`
(`mdtests/a_selective_import_cannot_clash_with_a_file_declaration.md`).
Types and constructors such as `Nat`, `List` and `List::Cons` keep their
bare names, as does the primitive conversion `to_nat`. When `click expand`
writes out a theorem of these modules, it spells it by its bare name when a
selective import brings it, and otherwise as `nat::name` or `list::name`.
Other modules still carry name prefixes, such as `cstr_len`, and their bare
names keep working until each is renamed; see
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
