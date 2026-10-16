// C strings, measured as C measures them: a length is a `size_t`. A string
// of length `len` occupies `len + 1` bytes, so `len` is below `SIZE_MAX`,
// which also keeps `len + 1` exact.
predicate prefix(bytes: uint8[], len: uint64) {
    forall (k: uint64) { k < len implies bytes[k] != '\0' }
}

predicate len(bytes: uint8[], len: uint64) {
    len < 18446744073709551615u64 and
        viewable(bytes[0..len + 1u64]) and
        cstr::prefix(bytes, len) and
        bytes[len] == '\0'
}

predicate cstr(bytes: uint8[]) {
    exists (len: uint64) {
        cstr::len(bytes, len)
    }
}

predicate readable_len(bytes: uint8[], len: uint64) {
    len < 18446744073709551615u64 and
        viewable(bytes[0..len + 1u64]) and
        forall (k: uint64) { k < len implies bytes[k] != '\0' } and
        bytes[len] == '\0' and
        forall (k: uint64) { k < len + 1u64 implies defined(bytes[k]) }
}

theorem readable_len_unique(bytes: uint8[], left: uint64, right: uint64) {
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
                    using { left < right; };
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
                            using { right < left; };
                        contradiction(bytes[right] == '\0');
                    }
                    not (right < left) => {
                        have left <= right by {
                            simp();
                        }
                        apply(uint64_less_equal_and_not_less_than_implies_equal(left, right)) using {
                            left <= right;
                            not (left < right);
                        };
                    }
                }
            }
        }
    }
}

predicate readable(bytes: uint8[]) {
    exists (len: uint64) {
        len < 18446744073709551615u64 and
            viewable(bytes[0..len + 1u64]) and
            forall (k: uint64) { k < len implies bytes[k] != '\0' } and
            bytes[len] == '\0' and
            forall (k: uint64) { k < len + 1u64 implies defined(bytes[k]) }
    }
}

// A C string: the bytes of `p` through its first terminator, with the facts
// that make them the C string of length `len`. The body owns the bytes; a
// contract chooses how it holds them: `views` borrows the string read-only,
// `owns` returns the same instance (so the same length), and `consumes` with
// `produces` changes it.
resource cstr_at(p: const uint8*, len: uint64) {
    owns p[0..len + 1u64];
    fact len < 18446744073709551615u64;
    fact forall (k: uint64) { 0u64 <= k and k < len implies p[k] != '\0' };
    fact p[len] == '\0';
    fact forall (k: uint64) { 0u64 <= k and k < len + 1u64 implies defined(p[k]) };
}

predicate bounded(bytes: uint8[], max: uint64) {
    exists (k: uint64) { k < max and bytes[k] == '\0' }
}

theorem len_is_viewable(bytes: uint8[], len: uint64) {
    requires cstr::len(bytes, len);

    ensures viewable(bytes[0..len + 1u64]) by {
        unfold(cstr::len);
        simp();
    }
}

theorem len_has_prefix(bytes: uint8[], len: uint64) {
    requires cstr::len(bytes, len);

    ensures cstr::prefix(bytes, len) by {
        unfold(cstr::len);
        simp();
    }
}

theorem len_has_terminator(bytes: uint8[], len: uint64) {
    requires cstr::len(bytes, len);

    ensures bytes[len] == '\0' by {
        unfold(cstr::len);
        simp();
    }
}
