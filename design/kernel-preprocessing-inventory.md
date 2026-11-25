# Pinned Linux rbtree preprocessing inventory

The [rbtree import fixture](../integrations/linux-rbtree/README.md) imports
the compiler-selected dependency closure from the pinned artifact. Keep
compiler options and source identity intact. The importer must refuse
unsupported retained input with an original-source diagnostic.
[Dependency-closure projection](../docs/reference/cli/capture.md#dependency-closure-projection)
claims only the declarations it retains.

The artifact `integrations/linux-rbtree/.click/captures/linux/lib/rbtree.c.i`
has 2,575 file-scope declarations from 138 files. The projection keeps 32,
which parse and lower as one unit (26 functions). Without projection the
frontend stops at `FIRST_REJECTION` in `linux_rbtree_tests.rs`:
`././include/linux/compiler_types.h:172: expected union name`, the anonymous
union member of the artifact's first declaration.

Per-declaration inventory, measured with `CLICK_LINUX_RBTREE_INVENTORY` (see
the integration README) at the commit that accepted the kernel's `inline`
attributes and unnamed prototype parameters. Forms accepted since, among them
`__builtin_constant_p`, `sizeof(expression)`, the empty `barrier()` assembly
and the `WRITE_ONCE` store, may have lowered these counts; re-measure before
relying on them. Each declaration reports its first rejection only, and one
that needs a rejected declaration is rejected too, so counts include
cascades and are lower bounds. 1,244 accepted, 1,331 rejected:

| Count | First rejection | Notes |
| ---: | --- | --- |
| 368 | unknown type name | `__signed__` and cascades through the fixed-width typedef chain, `atomic_long_t`, `atomic64_t`, `va_list` |
| 200 | file-scope form (`expected function declaration`) | mostly cascades; file-scope `asm(...)` 12 (the exports), `_Static_assert` 9, `register ... asm("rsp")` 1 |
| 178 | declarator form | function-pointer declarators, pointer returns of rejected types |
| 80 | statement form | inline `asm` statements 70, others 10 |
| 67 | unsupported file-scope object form | includes the twelve `extern typeof(fn) fn;` export redeclarations |
| 64 | unsupported builtin | `__builtin_constant_p` 56, `__builtin_bswap32` 4, `__builtin_bswap16` 2, `__builtin_mul_overflow` 2 |
| 58 | function attribute | `__format__` 26, `section` 14, `__warn_unused_result__` 4, `__externally_visible__` 4, `__error__` 4, `nocf_check` 2, `__alloc_size__` 2, `__pure__` 1, `__malloc__` 1 |
| 57 | unknown or embedded struct | cascades |
| 53 | undeclared identifier | `__noreturn__` 14 from `compiletime_assert`; the rest cascade |
| 45 | declarator tail | attribute between type and declarator, bitfields, array bounds with arithmetic or `sizeof` |
| 42 | field access through an incomplete struct | cascades |
| 12 | function-pointer typedef name | |
| 11 | anonymous `union` or `struct` member | the gate's pin |
| 96 | further forms, at most nine each | call sequencing, casts, enum parameters and returns, `packed`, empty structs, const forms, conditional typing |

When a frontend change moves the pin, update `FIRST_REJECTION` and this
table in the same change ([testing](../docs/internals/testing.md)).

Inline assembly other than the empty `barrier()`, export storage, and
`section` placement have storage or execution effects and must be modeled or
stay refused, not classified as metadata.
