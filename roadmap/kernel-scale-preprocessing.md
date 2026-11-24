# Import kernel-scale preprocessed translation units

Priority: P2. The delivered importer and the dependency-closure projection
are sufficient for the rbtree demo. Importing a whole kernel translation unit
does not block it.

Soundness: incomplete. Every unsupported GNU form or declaration in the
pinned Linux input is refused with a located diagnostic. Declarations outside
a projected closure are neither parsed for semantics nor claimed. The
compiler preprocessor is a trusted source-selection step
([trust](../docs/concepts/trust.md)), not an open gap of this item.

## Violated invariant

The C that Click verifies must be the active translation unit the configured
compiler selects. Unsupported input must be refused, never edited, skipped or
replaced with verifier-friendly macro bodies. Today that holds for the
pinned rbtree unit only through
[dependency-closure projection](../docs/reference/cli/capture.md#dependency-closure-projection):
the whole preprocessed unit does not parse, so a function whose closure
reaches an unsupported kernel declaration cannot be imported.

## Delivered

Documented in [`click capture`](../docs/reference/cli/capture.md) and
[the Linux rbtree closure](../integrations/linux-rbtree/README.md); not
repeated here:

- Project units in `click.project.json` with the lock and artifacts under
  `.click/captures/`; the old per-sidecar `<sidecar>.import.json` is refused
  (`per_sidecar_config_refusal` in `src/cli.rs`). Fresh reproduction against
  the lock, the ABI probe, bounded compiler runs, and offline load are in
  `src/languages/c/compiler_import.rs`.
- Line-marker source maps (`src/languages/c/source_map.rs`) and the checked
  projection (`src/languages/c/projection.rs`).
- The `linux-6.8-x86_64-kbuild` option profile, which accepts the recorded
  Linux 6.8.12 / GCC 13.3.0 vector unchanged, and the optimizer-promise
  refusal ([capture.md](../docs/reference/cli/capture.md#optimizer-promises)).
- The focused fixture `tests/fixtures/compiler-import/` with its gate
  `tests/compiler_import.rs`, and the pinned closure
  `integrations/linux-rbtree/` with its gate
  `src/languages/c/linux_rbtree_tests.rs`.
- Imports refuse `--changed-since` and bypass verification markers, a
  conservative answer to incremental reuse.
- Multi-size work checks for line-marker decoding
  (`decode_and_lookup_scale_across_four_input_sizes`), projection
  (`projection_work_is_linear_in_the_unit`) and root inventory
  (`root_inventory_scales_once_per_selected_file`). They are module tests,
  not in `src/scaling_tests/`.

Target and flag validation beyond the one profile belongs to
[multiple-compilers.md](multiple-compilers.md). Attaching proofs to the
pinned unit is rbtree launch work in [rbtree-example.md](rbtree-example.md).

## Remaining

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

## Intended regression

`linux_rbtree_locked_artifact_frontier` with the projection removed: the
whole pinned unit parses and lowers, and its test asserts the declaration
and function inventory instead of `FIRST_REJECTION`. Each form accepted on
the way gets an unchanged-source fixture and a near-miss rejection.

## Acceptance criteria

- The unprojected pinned unit parses and lowers with no change to upstream
  sources, the recorded options, or the lock; every retained executable
  construct has modeled semantics.
- Deterministic scaling checks at N, 2N, 4N and 8N cover parsing and
  lowering by declaration count and by functions sharing one import, in
  `src/scaling_tests/`.
- [Supported C](../docs/reference/language/c.md) and
  [`click capture`](../docs/reference/cli/capture.md) describe the accepted
  forms; `scripts/check.sh` passes.
