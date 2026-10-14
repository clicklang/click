// Byte ranges are measured as C measures them: an index or count is a
// `size_t`. `byte_count` keeps 32-bit bounds: a C-valued fold over `size_t`
// indices is not yet evaluated (bugs/uint64-c-valued-range-fold-drops-every-path.md).
function byte_count(bytes: uint8[], lo: int32, hi: int32, value: uint8) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + if bytes[k] == value { 1 } else { 0 }
    })
}

predicate bytes_equal(left: uint8[], left_lo: uint64, right: uint8[], right_lo: uint64, len: uint64) {
    (0u64..len).all(|k| {
        left[left_lo + k] == right[right_lo + k]
    })
}

predicate bytes_equal_range(left: uint8[], right: uint8[], lo: uint64, hi: uint64) {
    (lo..hi).all(|k| {
        left[k] == right[k]
    })
}

predicate bytes_all_equal(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) {
    (lo..hi).all(|k| {
        bytes[k] == value
    })
}

predicate bytes_contains(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) {
    (lo..hi).any(|k| {
        bytes[k] == value
    })
}

predicate bytes_all_not_equal(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) {
    (lo..hi).all(|k| {
        bytes[k] != value
    })
}
