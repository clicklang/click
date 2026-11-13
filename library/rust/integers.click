// The contracts of the Rust integer core methods, one `extern fn` per
// method and type: a call of `a.min(b)` on `u32` in imported Rust is a call
// of `u32::min`, whose result is the specification function of the same
// path in the library module `click::rust::u32` (`library/rust/u32.click`),
// opaque until a proof unfolds it. This file is not a module: the Rust
// importer appends to a sidecar the contract of each method an import
// calls, and only those, so each stays on one line. A signed type's
// `abs_diff` and `unsigned_abs` return the unsigned type of its width, and
// `checked_add` and `checked_sub` an `Option`.

extern fn i8::min(a: i8, b: i8) -> i8 { ensures result == click::rust::i8::min(a, b); }
extern fn i8::max(a: i8, b: i8) -> i8 { ensures result == click::rust::i8::max(a, b); }
extern fn i8::wrapping_add(a: i8, b: i8) -> i8 { ensures result == click::rust::i8::wrapping_add(a, b); }
extern fn i8::wrapping_sub(a: i8, b: i8) -> i8 { ensures result == click::rust::i8::wrapping_sub(a, b); }
extern fn i8::wrapping_mul(a: i8, b: i8) -> i8 { ensures result == click::rust::i8::wrapping_mul(a, b); }
extern fn i8::saturating_add(a: i8, b: i8) -> i8 { ensures result == click::rust::i8::saturating_add(a, b); }
extern fn i8::saturating_sub(a: i8, b: i8) -> i8 { ensures result == click::rust::i8::saturating_sub(a, b); }
extern fn i8::checked_add(a: i8, b: i8) -> Option<i8> { ensures result == click::rust::i8::checked_add(a, b); }
extern fn i8::checked_sub(a: i8, b: i8) -> Option<i8> { ensures result == click::rust::i8::checked_sub(a, b); }
extern fn i8::abs_diff(a: i8, b: i8) -> u8 { ensures result == click::rust::i8::abs_diff(a, b); }
extern fn i8::unsigned_abs(a: i8) -> u8 { ensures result == click::rust::i8::unsigned_abs(a); }

extern fn i16::min(a: i16, b: i16) -> i16 { ensures result == click::rust::i16::min(a, b); }
extern fn i16::max(a: i16, b: i16) -> i16 { ensures result == click::rust::i16::max(a, b); }
extern fn i16::wrapping_add(a: i16, b: i16) -> i16 { ensures result == click::rust::i16::wrapping_add(a, b); }
extern fn i16::wrapping_sub(a: i16, b: i16) -> i16 { ensures result == click::rust::i16::wrapping_sub(a, b); }
extern fn i16::wrapping_mul(a: i16, b: i16) -> i16 { ensures result == click::rust::i16::wrapping_mul(a, b); }
extern fn i16::saturating_add(a: i16, b: i16) -> i16 { ensures result == click::rust::i16::saturating_add(a, b); }
extern fn i16::saturating_sub(a: i16, b: i16) -> i16 { ensures result == click::rust::i16::saturating_sub(a, b); }
extern fn i16::checked_add(a: i16, b: i16) -> Option<i16> { ensures result == click::rust::i16::checked_add(a, b); }
extern fn i16::checked_sub(a: i16, b: i16) -> Option<i16> { ensures result == click::rust::i16::checked_sub(a, b); }
extern fn i16::abs_diff(a: i16, b: i16) -> u16 { ensures result == click::rust::i16::abs_diff(a, b); }
extern fn i16::unsigned_abs(a: i16) -> u16 { ensures result == click::rust::i16::unsigned_abs(a); }

extern fn i32::min(a: i32, b: i32) -> i32 { ensures result == click::rust::i32::min(a, b); }
extern fn i32::max(a: i32, b: i32) -> i32 { ensures result == click::rust::i32::max(a, b); }
extern fn i32::wrapping_add(a: i32, b: i32) -> i32 { ensures result == click::rust::i32::wrapping_add(a, b); }
extern fn i32::wrapping_sub(a: i32, b: i32) -> i32 { ensures result == click::rust::i32::wrapping_sub(a, b); }
extern fn i32::wrapping_mul(a: i32, b: i32) -> i32 { ensures result == click::rust::i32::wrapping_mul(a, b); }
extern fn i32::saturating_add(a: i32, b: i32) -> i32 { ensures result == click::rust::i32::saturating_add(a, b); }
extern fn i32::saturating_sub(a: i32, b: i32) -> i32 { ensures result == click::rust::i32::saturating_sub(a, b); }
extern fn i32::checked_add(a: i32, b: i32) -> Option<i32> { ensures result == click::rust::i32::checked_add(a, b); }
extern fn i32::checked_sub(a: i32, b: i32) -> Option<i32> { ensures result == click::rust::i32::checked_sub(a, b); }
extern fn i32::abs_diff(a: i32, b: i32) -> u32 { ensures result == click::rust::i32::abs_diff(a, b); }
extern fn i32::unsigned_abs(a: i32) -> u32 { ensures result == click::rust::i32::unsigned_abs(a); }

extern fn i64::min(a: i64, b: i64) -> i64 { ensures result == click::rust::i64::min(a, b); }
extern fn i64::max(a: i64, b: i64) -> i64 { ensures result == click::rust::i64::max(a, b); }
extern fn i64::wrapping_add(a: i64, b: i64) -> i64 { ensures result == click::rust::i64::wrapping_add(a, b); }
extern fn i64::wrapping_sub(a: i64, b: i64) -> i64 { ensures result == click::rust::i64::wrapping_sub(a, b); }
extern fn i64::wrapping_mul(a: i64, b: i64) -> i64 { ensures result == click::rust::i64::wrapping_mul(a, b); }
extern fn i64::saturating_add(a: i64, b: i64) -> i64 { ensures result == click::rust::i64::saturating_add(a, b); }
extern fn i64::saturating_sub(a: i64, b: i64) -> i64 { ensures result == click::rust::i64::saturating_sub(a, b); }
extern fn i64::checked_add(a: i64, b: i64) -> Option<i64> { ensures result == click::rust::i64::checked_add(a, b); }
extern fn i64::checked_sub(a: i64, b: i64) -> Option<i64> { ensures result == click::rust::i64::checked_sub(a, b); }
extern fn i64::abs_diff(a: i64, b: i64) -> u64 { ensures result == click::rust::i64::abs_diff(a, b); }
extern fn i64::unsigned_abs(a: i64) -> u64 { ensures result == click::rust::i64::unsigned_abs(a); }

extern fn isize::min(a: isize, b: isize) -> isize { ensures result == click::rust::isize::min(a, b); }
extern fn isize::max(a: isize, b: isize) -> isize { ensures result == click::rust::isize::max(a, b); }
extern fn isize::wrapping_add(a: isize, b: isize) -> isize { ensures result == click::rust::isize::wrapping_add(a, b); }
extern fn isize::wrapping_sub(a: isize, b: isize) -> isize { ensures result == click::rust::isize::wrapping_sub(a, b); }
extern fn isize::wrapping_mul(a: isize, b: isize) -> isize { ensures result == click::rust::isize::wrapping_mul(a, b); }
extern fn isize::saturating_add(a: isize, b: isize) -> isize { ensures result == click::rust::isize::saturating_add(a, b); }
extern fn isize::saturating_sub(a: isize, b: isize) -> isize { ensures result == click::rust::isize::saturating_sub(a, b); }
extern fn isize::checked_add(a: isize, b: isize) -> Option<isize> { ensures result == click::rust::isize::checked_add(a, b); }
extern fn isize::checked_sub(a: isize, b: isize) -> Option<isize> { ensures result == click::rust::isize::checked_sub(a, b); }
extern fn isize::abs_diff(a: isize, b: isize) -> usize { ensures result == click::rust::isize::abs_diff(a, b); }
extern fn isize::unsigned_abs(a: isize) -> usize { ensures result == click::rust::isize::unsigned_abs(a); }

extern fn u8::min(a: u8, b: u8) -> u8 { ensures result == click::rust::u8::min(a, b); }
extern fn u8::max(a: u8, b: u8) -> u8 { ensures result == click::rust::u8::max(a, b); }
extern fn u8::wrapping_add(a: u8, b: u8) -> u8 { ensures result == click::rust::u8::wrapping_add(a, b); }
extern fn u8::wrapping_sub(a: u8, b: u8) -> u8 { ensures result == click::rust::u8::wrapping_sub(a, b); }
extern fn u8::wrapping_mul(a: u8, b: u8) -> u8 { ensures result == click::rust::u8::wrapping_mul(a, b); }
extern fn u8::saturating_add(a: u8, b: u8) -> u8 { ensures result == click::rust::u8::saturating_add(a, b); }
extern fn u8::saturating_sub(a: u8, b: u8) -> u8 { ensures result == click::rust::u8::saturating_sub(a, b); }
extern fn u8::checked_add(a: u8, b: u8) -> Option<u8> { ensures result == click::rust::u8::checked_add(a, b); }
extern fn u8::checked_sub(a: u8, b: u8) -> Option<u8> { ensures result == click::rust::u8::checked_sub(a, b); }
extern fn u8::abs_diff(a: u8, b: u8) -> u8 { ensures result == click::rust::u8::abs_diff(a, b); }

extern fn u16::min(a: u16, b: u16) -> u16 { ensures result == click::rust::u16::min(a, b); }
extern fn u16::max(a: u16, b: u16) -> u16 { ensures result == click::rust::u16::max(a, b); }
extern fn u16::wrapping_add(a: u16, b: u16) -> u16 { ensures result == click::rust::u16::wrapping_add(a, b); }
extern fn u16::wrapping_sub(a: u16, b: u16) -> u16 { ensures result == click::rust::u16::wrapping_sub(a, b); }
extern fn u16::wrapping_mul(a: u16, b: u16) -> u16 { ensures result == click::rust::u16::wrapping_mul(a, b); }
extern fn u16::saturating_add(a: u16, b: u16) -> u16 { ensures result == click::rust::u16::saturating_add(a, b); }
extern fn u16::saturating_sub(a: u16, b: u16) -> u16 { ensures result == click::rust::u16::saturating_sub(a, b); }
extern fn u16::checked_add(a: u16, b: u16) -> Option<u16> { ensures result == click::rust::u16::checked_add(a, b); }
extern fn u16::checked_sub(a: u16, b: u16) -> Option<u16> { ensures result == click::rust::u16::checked_sub(a, b); }
extern fn u16::abs_diff(a: u16, b: u16) -> u16 { ensures result == click::rust::u16::abs_diff(a, b); }

extern fn u32::min(a: u32, b: u32) -> u32 { ensures result == click::rust::u32::min(a, b); }
extern fn u32::max(a: u32, b: u32) -> u32 { ensures result == click::rust::u32::max(a, b); }
extern fn u32::wrapping_add(a: u32, b: u32) -> u32 { ensures result == click::rust::u32::wrapping_add(a, b); }
extern fn u32::wrapping_sub(a: u32, b: u32) -> u32 { ensures result == click::rust::u32::wrapping_sub(a, b); }
extern fn u32::wrapping_mul(a: u32, b: u32) -> u32 { ensures result == click::rust::u32::wrapping_mul(a, b); }
extern fn u32::saturating_add(a: u32, b: u32) -> u32 { ensures result == click::rust::u32::saturating_add(a, b); }
extern fn u32::saturating_sub(a: u32, b: u32) -> u32 { ensures result == click::rust::u32::saturating_sub(a, b); }
extern fn u32::checked_add(a: u32, b: u32) -> Option<u32> { ensures result == click::rust::u32::checked_add(a, b); }
extern fn u32::checked_sub(a: u32, b: u32) -> Option<u32> { ensures result == click::rust::u32::checked_sub(a, b); }
extern fn u32::abs_diff(a: u32, b: u32) -> u32 { ensures result == click::rust::u32::abs_diff(a, b); }

extern fn u64::min(a: u64, b: u64) -> u64 { ensures result == click::rust::u64::min(a, b); }
extern fn u64::max(a: u64, b: u64) -> u64 { ensures result == click::rust::u64::max(a, b); }
extern fn u64::wrapping_add(a: u64, b: u64) -> u64 { ensures result == click::rust::u64::wrapping_add(a, b); }
extern fn u64::wrapping_sub(a: u64, b: u64) -> u64 { ensures result == click::rust::u64::wrapping_sub(a, b); }
extern fn u64::wrapping_mul(a: u64, b: u64) -> u64 { ensures result == click::rust::u64::wrapping_mul(a, b); }
extern fn u64::saturating_add(a: u64, b: u64) -> u64 { ensures result == click::rust::u64::saturating_add(a, b); }
extern fn u64::saturating_sub(a: u64, b: u64) -> u64 { ensures result == click::rust::u64::saturating_sub(a, b); }
extern fn u64::checked_add(a: u64, b: u64) -> Option<u64> { ensures result == click::rust::u64::checked_add(a, b); }
extern fn u64::checked_sub(a: u64, b: u64) -> Option<u64> { ensures result == click::rust::u64::checked_sub(a, b); }
extern fn u64::abs_diff(a: u64, b: u64) -> u64 { ensures result == click::rust::u64::abs_diff(a, b); }

extern fn usize::min(a: usize, b: usize) -> usize { ensures result == click::rust::usize::min(a, b); }
extern fn usize::max(a: usize, b: usize) -> usize { ensures result == click::rust::usize::max(a, b); }
extern fn usize::wrapping_add(a: usize, b: usize) -> usize { ensures result == click::rust::usize::wrapping_add(a, b); }
extern fn usize::wrapping_sub(a: usize, b: usize) -> usize { ensures result == click::rust::usize::wrapping_sub(a, b); }
extern fn usize::wrapping_mul(a: usize, b: usize) -> usize { ensures result == click::rust::usize::wrapping_mul(a, b); }
extern fn usize::saturating_add(a: usize, b: usize) -> usize { ensures result == click::rust::usize::saturating_add(a, b); }
extern fn usize::saturating_sub(a: usize, b: usize) -> usize { ensures result == click::rust::usize::saturating_sub(a, b); }
extern fn usize::checked_add(a: usize, b: usize) -> Option<usize> { ensures result == click::rust::usize::checked_add(a, b); }
extern fn usize::checked_sub(a: usize, b: usize) -> Option<usize> { ensures result == click::rust::usize::checked_sub(a, b); }
extern fn usize::abs_diff(a: usize, b: usize) -> usize { ensures result == click::rust::usize::abs_diff(a, b); }
