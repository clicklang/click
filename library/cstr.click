// C strings, measured as C measures them: a length is a `size_t`. A string
// of length `len` occupies `len + 1` bytes, so `len` is below `SIZE_MAX`,
// which also keeps `len + 1` exact.
predicate cstr_prefix(bytes: uint8[], len: uint64) {
    forall (k: uint64) { k < len implies bytes[k] != '\0' }
}

predicate cstr_len(bytes: uint8[], len: uint64) {
    len < 18446744073709551615u64 and
        viewable(bytes[0..len + 1u64]) and
        cstr_prefix(bytes, len) and
        bytes[len] == '\0'
}

predicate cstr(bytes: uint8[]) {
    exists (len: uint64) {
        cstr_len(bytes, len)
    }
}

predicate cstr_readable_len(bytes: uint8[], len: uint64) {
    len < 18446744073709551615u64 and
        viewable(bytes[0..len + 1u64]) and
        forall (k: uint64) { k < len implies bytes[k] != '\0' } and
        bytes[len] == '\0' and
        forall (k: uint64) { k < len + 1u64 implies defined(bytes[k]) }
}

theorem cstr_readable_len_unique(bytes: uint8[], left: uint64, right: uint64) {
    requires forall (k: uint64) { k < left implies bytes[k] != '\0' };
    requires bytes[left] == '\0';
    requires forall (k: uint64) { k < right implies bytes[k] != '\0' };
    requires bytes[right] == '\0';

    ensures left == right by {
        have left < right or not (left < right) by {
            if left < right {
                assumption();
            } else {
                assumption();
            }
        }
        cases {
            left < right => {
                instantiate(forall (k: uint64) { k < right implies bytes[k] != '\0' }, left)
                    using { left < right; }
                contradiction(bytes[left] == '\0');
            }
            not (left < right) => {
                have right < left or not (right < left) by {
                    if right < left {
                        assumption();
                    } else {
                        assumption();
                    }
                }
                cases {
                    right < left => {
                        instantiate(forall (k: uint64) { k < left implies bytes[k] != '\0' }, right)
                            using { right < left; }
                        contradiction(bytes[right] == '\0');
                    }
                    not (right < left) => {
                        have left <= right by {
                            simp();
                        }
                        apply(uint64_less_equal_and_not_less_than_implies_equal(left, right)) using {
                            left <= right;
                            not (left < right);
                        }
                    }
                }
            }
        }
    }
}

predicate cstr_readable(bytes: uint8[]) {
    exists (len: uint64) {
        len < 18446744073709551615u64 and
            viewable(bytes[0..len + 1u64]) and
            forall (k: uint64) { k < len implies bytes[k] != '\0' } and
            bytes[len] == '\0' and
            forall (k: uint64) { k < len + 1u64 implies defined(bytes[k]) }
    }
}

predicate cstr_bounded(bytes: uint8[], max: uint64) {
    exists (k: uint64) { k < max and bytes[k] == '\0' }
}

theorem cstr_len_is_viewable(bytes: uint8[], len: uint64) {
    requires cstr_len(bytes, len);

    ensures viewable(bytes[0..len + 1u64]) by {
        unfold(cstr_len);
        simp();
    }
}

theorem cstr_len_has_prefix(bytes: uint8[], len: uint64) {
    requires cstr_len(bytes, len);

    ensures cstr_prefix(bytes, len) by {
        unfold(cstr_len);
        simp();
    }
}

theorem cstr_len_has_terminator(bytes: uint8[], len: uint64) {
    requires cstr_len(bytes, len);

    ensures bytes[len] == '\0' by {
        unfold(cstr_len);
        simp();
    }
}
