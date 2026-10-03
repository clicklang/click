# Shared slices through IntoIterator

`sum.rs` and `sum.click` are byte-for-byte copies of the unchanged
`rust-iterators` fixture. Its implicit `for &byte in bytes` now imports through
Charon using the compiler-selected `IntoIterator for &[T]` implementation.
Its original proof still fails on `__rust_iter_3_5_remaining`, a legacy proof
observation; it remains a proof gap rather than a verified parity entry.

`iteration.rs` proves first-element reads from shared u8/i32/u32 slices and
passes an i32 slice through an ordinary source call. `iteration.click` covers
nonempty input and `empty.click` covers zero length without read permission.
False results and missing views fail. The iterator retains actual cursor,
remaining and live state, typed Option dispatch and checked memory reads;
it does not synthesize a processed count or replace the source loop.

The adapter checks the resolved core trait and implementation path, method
linkage, shared receiver, generic signature and concrete element type. Incoming
i32/u32 slices and source calls carry paired pointer/usize length values;
reborrows accept only matching metadata from the same pointer origin. Mutable
iteration, owned arrays and unmodeled iterator adapters remain rejected.
Lengths remain usize; iteration checks its signed-word memory-model extent
bound before narrowing. Metadata-name collisions fail promptly.

Regressions reject forged identities, signatures, mutability, instantiations,
and mismatched pointer/length origins. Deterministic checks at slice lengths
8/128/1024 confirm that initialization and first-read verification do not expand
with the extent. Verification, profiling, auditing, expansion and expanded
rechecking agree. The live suite re-extracts both sources, rechecks the frozen
proof gap, and retains compiler/borrow-checker and adapter rejections.

`shared-scalar-slice-into-iteration-v1` versions this added interpretation.
Existing artifact bytes, extraction flags and compiler pins are unchanged;
existing checkpoint locks are deliberately updated. External Charon locks
require explicit refresh.

The fixed 16-fixture inventory now imports 15/16 (93.75%), up from 14/16 (87.5%).
Frozen proof parity remains 10/16 (62.5%); coverage with the two previously
migrated proof sidecars remains 12/16 (75%). Tuple/slice-return normalization
blocks `rust-split-at`; stable iterator observations and frozen-selector
compatibility still block complete proof parity and the default switch.
