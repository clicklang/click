// Byte ranges are measured as C measures them: an index or count is a
// `size_t`. `bytes::count` keeps 32-bit bounds: a C-valued fold over `size_t`
// indices is not yet evaluated (bugs/uint64-c-valued-range-fold-drops-every-path.md).
function count(bytes: uint8[], lo: int32, hi: int32, value: uint8) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + if bytes[k] == value { 1 } else { 0 }
    })
}

predicate equal(left: uint8[], left_lo: uint64, right: uint8[], right_lo: uint64, len: uint64) {
    (0u64..len).all(|k| {
        left[left_lo + k] == right[right_lo + k]
    })
}

predicate equal_range(left: uint8[], right: uint8[], lo: uint64, hi: uint64) {
    (lo..hi).all(|k| {
        left[k] == right[k]
    })
}

predicate all_equal(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) {
    (lo..hi).all(|k| {
        bytes[k] == value
    })
}

predicate contains(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) {
    (lo..hi).any(|k| {
        bytes[k] == value
    })
}

predicate all_not_equal(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) {
    (lo..hi).all(|k| {
        bytes[k] != value
    })
}

// The sign of a byte comparison follows its first differing unsigned byte.
predicate comparison(left: uint8[], right: uint8[], length: uint64, cmp: int32) {
    (cmp == 0 implies bytes::equal(left, 0u64, right, 0u64, length)) and
    (cmp != 0 implies not bytes::equal(left, 0u64, right, 0u64, length)) and
    forall (k: uint64) {
        k < length and bytes::equal_range(left, right, 0u64, k) implies
            (left[k] < right[k] implies cmp < 0) and
            (right[k] < left[k] implies cmp > 0)
    }
}

theorem comparison_negative_after_prefix(left: uint8[], right: uint8[], length: uint64, first: uint64, cmp: int32) {
    requires bytes::comparison(left, right, length, cmp);
    requires first < length;
    requires bytes::equal_range(left, right, 0u64, first);
    requires left[first] < right[first];
    ensures cmp < 0 by {
        unfold(bytes::comparison(left, right, length, cmp));
        instantiate(forall (k: uint64) {
            k < length and bytes::equal_range(left, right, 0u64, k) implies
                (left[k] < right[k] implies cmp < 0) and
                (right[k] < left[k] implies cmp > 0)
        }, first);
        solve();
    }
}

theorem comparison_positive_after_prefix(left: uint8[], right: uint8[], length: uint64, first: uint64, cmp: int32) {
    requires bytes::comparison(left, right, length, cmp);
    requires first < length;
    requires bytes::equal_range(left, right, 0u64, first);
    requires right[first] < left[first];
    ensures cmp > 0 by {
        unfold(bytes::comparison(left, right, length, cmp));
        instantiate(forall (k: uint64) {
            k < length and bytes::equal_range(left, right, 0u64, k) implies
                (left[k] < right[k] implies cmp < 0) and
                (right[k] < left[k] implies cmp > 0)
        }, first);
        solve();
    }
}

theorem comparison_zero_when_equal(left: uint8[], right: uint8[], length: uint64, cmp: int32) {
    requires bytes::comparison(left, right, length, cmp);
    requires bytes::equal(left, 0u64, right, 0u64, length);
    ensures cmp == 0 by {
        unfold(bytes::comparison(left, right, length, cmp));
        solve();
    }
}
