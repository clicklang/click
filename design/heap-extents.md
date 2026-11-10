# Heap-block extents: 64-bit (`size_t`) sizes

Status: option (a) accepted by the maintainer, 2026-11-10 (decisions D1-D6
below). PR 0 (this note and a bug fix) has landed. Line numbers are at
`origin/master` b247d7499 plus PR 0's changes (`statements.rs`,
`primitives.rs`).

This is the kernel prerequisite for `roadmap/standard-library.md` step 7,
"`size_t` sizes for `allocation`", and its intended regression ("an
`allocation` client whose byte count comes from a `size_t` expression, with no
narrowing to `int32`"). It finishes [typed-indices](typed-indices.md) stage 2
("The extent is `isize::MAX`") for heap blocks: stage 2 made contract ranges
wide (`RangeIndexKind::UInt64`, `src/kernel/primitives.rs:5589`) with the
extent fact `end <= i64::MAX / w` (`wide_memory_range_extent_guards`,
`src/kernel/primitives/contracts.rs:3250`), but left heap blocks 32-bit. Its
rulings apply: narrowing a 64-bit index into a 32-bit range is a dead end, a
64-bit index is never narrowed, and a range's kind does not depend on what a
contract happens to prove.

## 1. Current model

- **Token.** `abstract resource allocation(base: int32*, bytes: int32);`
  (`library/primitives.click:7`); the surface injects the same types
  (`src/surface/validation/declaration_expansion.rs:920-926`). In the kernel
  it is a `CResource::Token` with `[CValue::Pointer(base), CValue::Int32(bytes)]`:
  `own_allocation` / `own_designated_allocation`
  (`src/kernel/primitives/resource_algebra.rs:11544-11559`, wrapping bytes in
  `int32(..)`); `allocation_bounds_fact` (`:11562-11590`) and
  `allocation_value` (`:11593-11609`) match `CValue::Int32` only. The token
  carries lifetime and free authority, not access.
- **Access.** A separate owned range `p[0..count]`, built by
  `resolve_pending_heap_allocations` (`src/kernel/eval/statements.rs:2560-2705`)
  with `CMemoryRange::new_with_element_width`, so always
  `RangeIndexKind::Int32`. Its width is the pointee width when the byte count
  is `k*w` or a multiple of `w`, else bytes (`heap_range_element_width/_count`,
  `statements.rs:1501-1512`, via `element_count_from_bytes`,
  `src/kernel/reasoning/path_facts.rs:834-861`, which matches only an Int32
  `Multiply` or a 32-bit constant).
- **Heap state.** `CHeapMemory` (`src/kernel/primitives.rs:8495-8542`) maps
  pointers to untyped `MachineTerm` extents (live, deallocated, pending,
  zeroed-prefix); so do `CPendingReallocation.old_bytes` and `CBlock.size`
  (`primitives.rs:8675-8677`). The width is implicit; `memory_state.rs:4008`
  labels a reallocation's old bytes `CValue::Int32`.
- **Offsets** are already width-typed (`PointerOffsetTerm::Int32Scaled` /
  `Int64Scaled{unsigned}`, `primitives.rs:1018-1035`). `pointer_index_term`
  (`src/kernel/eval/operators.rs:2419-2446`) keeps a `size_t` index 64-bit and
  always zero-extends `uint32`. `pointer_block_bounds` (`operators.rs:2884-2990`)
  reads `CBlock.size` as unsigned 32 bits in its wide arms and as `int32` in
  its narrow arm.
- **malloc/calloc.** `execute_c_heap_allocate_paths` (`statements.rs:1288-1474`).
  The C front end lowers `calloc(n, w)` to `Multiply(n, w)` with
  `zeroed = true` (`src/languages/c/syntax.rs:14703-14826`).
  `heap_element_count_expression` (`statements.rs:1590-1607`) recognizes
  `e * w` / `w * e` syntactically and evaluates only `e`. `allocation_size_value`
  (`:1538-1588`) admits every value of 32 bits or narrower symbolically, and
  `Int64`/`UInt64` only when `exact_signed/unsigned_size_value` (`:1609-1685`)
  reduce it to a constant that fits `u32` (directly, through fact-proven
  equalities, or by `+ - *` of such constants). The element path decides
  positivity and `n <= i32::MAX / w` (`allocation_size_validity_refusal`,
  `:1687-1738`) and forms the Int32 `multiply(n, w)`; the raw path decides
  positivity, and for a `uint32` also `bytes <= INT32_MAX` (PR 0). The
  object-class check (`enough_space`, `:1414-1417`) is a 32-bit compare.
- **realloc** (`execute_c_realloc_assign_paths`, `statements.rs:1740-2253`)
  repeats the admission (`:1929-1979`); its prefix-preservation conditions are
  32-bit compares keyed on `AllocationSize.unsigned` (`:2119-2184`); a zeroed
  prefix must be constant (`:1981-2006`); `realloc(NULL, n)` reuses malloc.
- **free** (`execute_c_heap_free_paths`, `statements.rs:2255`) finds the token
  by base (`own_designated_allocation(pointer, 0)`, `:2308`), then consumes it
  and the full byte range `new_with_element_width(p, 0, bytes, 1)`
  (`:2403-2409`), independent of how the extent was spelled.
- **Contracts.** `allocation(result, e)` in a contract is evaluated at
  `src/kernel/functions.rs:19235-19300`, with its own `e * 4` shortcut that
  matches only the `int32` literal and a `CValue::Int32` count. `allocation`
  cannot be viewed (`declaration_expansion.rs:2846`); a symbolic quantity is
  refused (`functions.rs:18936`). Argument 0 accepts any data-pointer type
  (`src/surface/validation/type_validation.rs:3070-3090`); argument 1 has a
  64-bit refusal hint (`:3055-3066`).
- **Ranges** of `Int32` kind are capped at a `u32` byte count
  (`memory_range_element_count_limit`, `contracts.rs:2830`;
  `memory_range_byte_count_extent`, `:2905`); wide ones at `i64::MAX / w`. The
  ordered interval index uses signed-32 coordinates
  (`resource_algebra.rs:145`, `:1150-1182`), and `concrete_memory_range_bounds`
  gives up on wide ranges (`contracts.rs:2433-2439`): wide ranges are never
  interval-indexed.
- **Diagnostic.** `CRuntimeError::HeapAllocationSize` (`primitives.rs:7406`,
  message `:7747`; `HeapAllocationSizeAboveInt32` beside them;
  `src/surface/diagnostics.rs:1662`;
  `src/kernel/api/contract_certification.rs:841`).
- **Docs.** `docs/reference/language/c.md:2154-2159, 2606-2650, 2675-2681`,
  `docs/reference/language/index.md:2820` ("checked 32-bit extent").

Why 32-bit: the heap model predates typed indices, when every range was
`Int32`; stage 2 widened contract ranges and left the heap constructor alone
(comment at `statements.rs:1532-1537`). 085788448 (2026-11-07) added
`HeapAllocationSize`.

### Sites a 64-bit extent touches

| Site | 32-bit today |
|---|---|
| `library/primitives.click:7`, `declaration_expansion.rs:926` | `bytes: int32` |
| `type_validation.rs:3055-3066` | 64-bit refusal hint |
| `resource_algebra.rs:11544-11609` | token built and matched as `CValue::Int32` |
| `resource_algebra.rs:11623-11660`, `path_facts.rs:834-861` | separation via `element_count_from_bytes` (Int32 only) |
| `statements.rs:1372-1417` | `multiply(n, w)` Int32; `enough_space` |
| `statements.rs:1501-1738` | element width/count, size admission, positivity/fit |
| `statements.rs:1929-2006, 2119-2184` | realloc admission and fit compares |
| `statements.rs:2308, 2403-2409, 2560-2705` | free's range and token; pending resolution |
| `primitives.rs:8495-8542, 8675-8677`; `memory_state.rs:3582-3587, 3946-3980, 4008` | untyped extents, implicit 32-bit reading |
| `operators.rs:2884-2990` | `pointer_block_bounds` |
| `functions.rs:19235-19300` | contract `allocation(p, e*4)` |
| `resource_algebra.rs:145, 1177-1182` | interval-index coordinates (not heap-specific) |

### Corpus

No integration (bitcoin money range, linux rbtree, libcxx fixtures) allocates
on the heap; C++ `new` and Rust `Box` lower to a constant
`c_int32_literal(size)`. Constant sizes (`sizeof(T)`, `k * sizeof(T)`,
literals) dominate; they are 64-bit constants the exact-constant path admits.
About 15 call sites use a symbolic `int32` count with an explicit
`count <= INT_MAX / w` requirement. The only `size_t` clients
(`mdtests/integer_heap_widths.md`) pin `count == 2/3`. No fixture allocates a
bounded symbolic `size_t`, although `malloc(n * sizeof *p)`, `malloc(len + 1)`
and `calloc(n, sizeof(T))` with `size_t n` are the idiomatic forms. All 127
`allocation(` sidecars use `int32` or constant byte counts; extern allocators
with a `size_t` extent write `bytes as int32`
(`an_extern_allocator_states_a_bounded_64_bit_extent_as_int32.md`).

### Probes (2026-11-10, debug binary at 17fb0ad3c)

- Refused with `HeapAllocationSize`, all with bounded `size_t` sizes:
  `malloc(n * sizeof(uint32_t))` (`1 <= n <= 100`); `calloc(n, sizeof(uint16_t))`
  (shown as `calloc((n * 2u64))`); `realloc(data, n * sizeof(uint64_t))`;
  the overflow-safe cast `malloc((size_t)count * sizeof(uint32_t))` with
  `int count`; `malloc(len + 1)` with `len <= 4096`.
- Extern allocator `produces allocation(result, bytes);` with `size_t bytes`:
  type error, "resource `allocation` argument 1 expects int32, got uint64".
- Control: `int n`, `malloc(n * sizeof(uint32_t))`, store, read, free: passes.
- A wide parameter range (`owns bytes[0..length]`, `uint64 length`) already
  accepts an `int32` index: passes.
- `produces allocation(result, bytes as int32); produces result[0..bytes];`
  (wide range beside an `int32` token), then `data[n - 1]` with a `size_t`
  index and `free`: passes; free's Int32 full-range request is met by the wide
  range. One byte short: free refused with `missing resource fact owns
  ((char *)data)[0..(n as uint32)]`. Cross-kind consumption is checked.
- `abstract resource sized(p: int32*, k: Integer);`: "algebraic resource
  arguments are not supported yet" (blocks option (c)).
- `uint32` size `>= 2^31` (`malloc(n)` with `n == 3000000000u32`): accepted,
  then `p[0]` refused as "pointer arithmetic left the pointed-to object"; the
  resources showed `allocation(p, int32(n))` and `p[Int32:0..n]`. Fixed in PR 0.

## 2. Constraints every option respects

- `size_t` arithmetic wraps without UB: `malloc(n * w)` allocates
  `(n*w) mod 2^64`, a real block. Reading `e*w` as an exact product needs a
  decided no-wrap condition; otherwise the C product itself is evaluated.
- `calloc(n, w)` returns null when `n*w` is not representable (C17 7.22.3.2,
  explicit in C23). Click lowers it to `Multiply(n, w)`, safe only while the
  kernel never evaluates that as a wrapping product.
- An object above `PTRDIFF_MAX` bytes makes pointer subtraction within it
  undefined (C17 6.5.6p9). Click's wide-range extent is `end <= i64::MAX / w`,
  so a 64-bit block's ceiling is `PTRDIFF_MAX` bytes, proved at the allocation
  (not assumed at entry, as contracts are).

## 3. Options

- **(a) Accepted. A tagged extent `HeapExtent { term, kind: Int32 | UInt64 }`.**
  The kind comes from the size's C type. Every 32-bit and narrower value and
  every term-constant 64-bit value that fits stays `Int32`; a symbolic
  `Int64`/`UInt64` value is `UInt64` (a signed one read as its sign extension,
  so a negative one fails the extent guard). The `UInt64` block's token holds
  `CValue::UInt64`, its range is `new_wide`, and accesses use the existing
  `Int64Scaled` offsets and wide membership, as wide parameter ranges do.
  Constant-size blocks stay `Int32` and interval-indexed.
- (b) Rejected (D6): keep 32-bit and narrow a bounded `size_t` under
  `E <= i32::MAX`. Smallest change, but it is the narrowing typed-indices
  ruled out, caps blocks at 2 GiB, makes acceptance fact-dependent, and needs
  the `n as int32` round-trip rule.
- (c) Deferred: an `Integer` extent. Needs Integer resource arguments
  (refused today), still needs a machine range kind, and moves Integer
  reasoning into resource-argument equality on the hot path.
- (d) Rejected (D1): one uniform `UInt64` heap kind. Moves every constant-size
  block out of the interval index and changes every heap token spelling.
- (e) Rejected (D3): a trusted allocator-limit model (null above
  `PTRDIFF_MAX`).

## 4. Decisions (maintainer, 2026-11-10)

- **D1.** Extent width by the size's C type, as in (a).
- **D2.** A `size_t` size the facts fix to a constant (`requires count == 2`,
  `integer_heap_widths.md`) stays a 32-bit constant extent, as today.
- **D3.** An unbounded `size_t` size must be proved `bytes <= PTRDIFF_MAX` at
  the allocation; there is no trusted "returns null" assumption.
- **D4.** `allocation`'s byte count stays declared `int32` and also accepts
  `uint64`, mirroring argument 0's pointer-type independence.
- **D5.** A 32-bit size spelled against a 64-bit block's `allocation` resource
  is refused with a message naming the kinds; no cross-kind argument equality.
- **D6.** No 32-bit narrowing stopgap ((b) does not ship). The
  extern-allocator `bytes as int32` form stays legal and means what it says.

A `uint32` size stays `Int32` under D1, so one above `INT32_MAX` stays refused
after PR 2; accepting it would need a separate decision to give `uint32` sizes
the `UInt64` kind.

## 5. Staged plan

0. **Landed: bug fix and this note.** `allocation_size_value` admitted a
   `uint32` size as unsigned, deciding only positivity or `n <= u32::MAX / w`,
   and stored it in the `int32` token and Int32 range, where `>= 2^31` read
   negative. A `uint32` size (`AllocationSize.needs_extent_bound`) must now be
   decided at most `INT32_MAX` bytes (raw) or `INT32_MAX / w` elements, for
   `malloc`, `calloc` and `realloc`; otherwise the allocation is refused with
   `CRuntimeError::HeapAllocationSizeAboveInt32`. Regressions:
   `mdtests/a_uint32_malloc_size_above_int32_max_is_refused_at_the_malloc.md`,
   `a_uint32_element_count_above_the_int32_heap_extent_is_refused.md`,
   `a_uint32_realloc_size_above_int32_max_is_refused_at_the_realloc.md`,
   `a_uint32_malloc_size_bounded_by_int32_max_allocates.md`.
1. **Tagged extent, no behavior change.** `HeapExtent { term, kind }` in
   `CHeapMemory`, `CPendingReallocation`, `CBlock`, the token constructors and
   `AllocationSize`, all `Int32`. Gate green; `memory_scaling_tests` work
   counts unchanged.
2. **Kernel 64-bit malloc and free, with the size proof.** Symbolic
   `UInt64`/`Int64` sizes: raw path decides `0 < E <= i64::MAX`; element path
   decides `1 <= n <= i64::MAX / w` and forms the exact `uint64 multiply(n, w)`;
   if that guard is undecided, malloc evaluates the C product as the raw size
   (a wrapped value is a real block). `new_wide` range, `UInt64` token,
   kind-aware free, `pointer_block_bounds` reads a `UInt64` size as `uint64`,
   `element_count_from_bytes` gains a `UInt64 Multiply` / `uint64` constant
   arm, `enough_space` in the size's format, separation through the widened
   `element_count_from_bytes`. Message for an undecided guard names the
   `PTRDIFF_MAX` bound (D3). Regressions (mdtests):
   - bounded `size_t` `malloc(n * sizeof(uint32_t))`, `p[n - 1]` written and freed;
   - `malloc(len + 1)`, `p[len] = 0`; `malloc((size_t)count * sizeof(T))`;
   - unbounded `size_t n` refused with the new message (replaces
     `a_symbolic_64_bit_malloc_size_names_the_32_bit_heap_extent.md`);
   - `n <= 2^62`, `malloc(n * 8)` refused (guard undecided);
   - `n == 2^62 + 1`, `malloc(n * 4)` is the wrapped 4-byte block; `p[1]` refused;
   - interior free and double free of a wide block refused.

   Kernel unit tests for the token and range kinds after resolution. Scaling:
   wide-heap copies of `normalizing_allocation_tokens_in_distinct_heap_blocks_is_linear`
   (`src/scaling_tests/kernel/tests/memory_scaling_tests.rs:349`),
   `one_heap_store_is_logarithmic_in_unrelated_allocations` (`:434`),
   `stores_beside_many_owned_ranges_scale_near_linearly`, and one of
   `src/scaling_tests/kernel/functions/allocation_continuity_tests.rs`, at
   N, 2N, 4N, 8N.
3. **Sidecar and contract 64-bit byte count, and docs.** `allocation` argument 1
   accepts `uint64` (D4: `primitives.click`, `declaration_expansion.rs:926`,
   `type_validation.rs:3055-3090`); `functions.rs:19235` accepts `n * 8u64` and
   a `CValue::UInt64` count under the same no-wrap decision. Docs: `c.md` heap
   and extern-allocator sections, the language-reference primitive entry, the
   library reference. Regressions: extern `produces allocation(result, bytes)`
   with `size_t bytes` and `result[0..bytes]` passes (replaces
   `an_extern_allocator_with_a_64_bit_extent_names_the_32_bit_heap_extent.md`);
   a callee `consumes allocation(p, n)` over a malloc'd wide block passes; an
   `int32` spelling against a `uint64` token is refused naming the kinds (D5);
   `an_extern_allocator_states_a_bounded_64_bit_extent_as_int32.md` unchanged.
   Closes the step 7 item and its intended regression.
4. **calloc and realloc.** calloc decides the guard and never evaluates its
   product; an undecided guard is refused. realloc: kind-aware fit conditions
   (`uint64_less_equal`) and a wide old range for removal; a constant zeroed
   prefix stays the supported case. Regressions: bounded `size_t` calloc and
   realloc pass; a calloc with an undecided guard is refused; shrink and grow
   of a wide block preserve the prefix; a wide realloc from a zeroed source.

Soundness of (a): a `UInt64` extent `E` is admitted only with `0 < E <= i64::MAX`
decided (raw) or `1 <= n <= i64::MAX / w` and `E = n*w` (element, no wrap, so
`E` is C's `size_t` value). Token and range both name `E`; the wide-range
extent guard holds by construction; wide membership makes the scaled offset
mathematical; calloc never evaluates its product; free and realloc consume
exactly the recorded kind and extent. No new trusted assumption
(`docs/concepts/trust.md:57-60, 97-101` already trusts the allocation model).

Out of scope: zero-size allocation, `void *` results, `aligned_alloc`,
`posix_memalign`, blocks above `PTRDIFF_MAX`, non-constant zeroed-prefix
realloc, Integer extents, moving `int32` or constant sizes to the wide kind,
ILP32 targets, C++ `new[]`, the Rust `Vec` model, and `byte_stride_index`.

The fact-dependent lowerings in `roadmap/standard-library.md` stay separate.
The byte-offset restride (`byte_stride_index`, `operators.rs`) applies only to
narrow signed displacements; wide heap blocks reach it only through 32-bit
`char` displacements, as parameter ranges do. Both it and (a) read a
`Multiply` as an exact product only under a decided no-wrap condition.
