# Shared slices through IntoIterator

`sum.rs` and `sum.click` mirror the canonical `examples/rust-iterators`
source and proof. The implicit `for &byte in bytes` imports through Charon
using the compiler-selected `IntoIterator for &[T]` implementation. The
proof tracks progress through `iter.len()` and proves the sum for the
original Rust body.

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
Lengths remain usize; iteration checks its signed-word memory-model span
bound before narrowing. Metadata-name collisions fail promptly.

Regressions reject forged identities, signatures, mutability, instantiations,
and mismatched pointer/length origins. Deterministic checks at slice lengths
8/128/1024 confirm that initialization and first-read verification do not expand
with the length. Verification, profiling, auditing, expansion and expanded
rechecking agree. The live suite re-extracts both sources, rechecks the sum proof, and retains compiler/borrow-checker and adapter rejections.

`shared-scalar-slice-into-iteration-v1` versions this added interpretation.
Existing artifact bytes, extraction flags and compiler pins are unchanged;
existing checkpoint locks are deliberately updated. External Charon locks
require explicit refresh.
