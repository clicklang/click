import click::separation;

theorem selected_array_cell(whole: Resource, kept: Resource, p: int32*, len: int32, i: int32) {
    requires separate(whole, memory(p[0..len]));
    requires contains(whole, kept);
    requires 0 <= i;
    requires i < len;
    ensures separate(kept, memory(p[i])) by {
        have i <= 2147483646 by { solve() using { i < len; }; }
        have defined(i + 1) by { solve() using { 0 <= i; i <= 2147483646; }; }
        have i <= ((i + 1) as int32) by { solve() using { 0 <= i; i < len; }; }
        have ((i + 1) as int32) <= len by { solve() using { 0 <= i; i < len; }; }
        have contains(memory(p[0..len]), memory(p[i..i + 1])) by {
            apply(separation::subrange(p, 0, len, i, i + 1)) using {
                defined(i + 1); 0 <= i; i <= ((i + 1) as int32); ((i + 1) as int32) <= len;
            };
        }
        have separate(kept, memory(p[i..i + 1])) by {
            apply(separation::restrict(whole, memory(p[0..len]), kept, memory(p[i..i + 1]))) using {
                defined(i + 1); separate(whole, memory(p[0..len])); contains(whole, kept);
                contains(memory(p[0..len]), memory(p[i..i + 1]));
            };
        }
        have contains(kept, kept) by { normalize(); }
        have contains(memory(p[i..i + 1]), memory(p[i])) by { normalize(); }
        apply(separation::restrict(kept, memory(p[i..i + 1]), kept, memory(p[i]))) using {
            defined(i + 1); separate(kept, memory(p[i..i + 1])); contains(kept, kept);
            contains(memory(p[i..i + 1]), memory(p[i]));
        };
    }
}

theorem int32_equality_transitive(first: int32, second: int32, third: int32) {
    requires first == second;
    requires second == third;

    ensures first == third by {
        solve();
    }
}

resource empty_vector(owner: struct vector*) {
    owns *owner;
    owns owner->data[0..owner->cap];
    fact owner->len == 0;
    fact 1 <= owner->cap;
    fact owner->cap <= 1073741823;
    fact separate(memory(*owner), memory(owner->data[0..owner->cap]));
}

resource nonempty_vector(owner: struct vector*) {
    owns *owner;
    owns owner->data[0..owner->cap];
    fact 1 <= owner->len;
    fact owner->len <= owner->cap;
    fact owner->cap <= 1073741823;
    fact separate(memory(*owner), memory(owner->data[0..owner->cap]));
}

resource vector_storage(owner: struct vector*) {
    owns *owner;
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
    fact owner->cap <= 1073741823;
    fact separate(memory(*owner), memory(owner->data[0..owner->cap]));
}

resource allocated_vector(owner: struct vector*) {
    owns *owner;
    owns allocation(owner->data, owner->cap * 4);
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
    fact 1 <= owner->cap;
    fact owner->cap <= 536870911;
    fact separate(memory(*owner), memory(owner->data[0..owner->cap]));
}

verifying "vector_init.c";
verifying "vector_len.c";
verifying "vector_get.c";
verifying "vector_set.c";
verifying "vector_fill.c";
verifying "vector_replace_if.c";
verifying "vector_clear.c";
verifying "vector_pipeline.c";
verifying "vector_copy.c";
verifying "vector_grow.c";
verifying "vector_push.c";
verifying "allocated_vector_push.c";

int32 vector_copy(
    int32 dst[],
    int32 src[],
    int32 length,
    int32 dst_capacity,
    int32 src_capacity
) {
    requires 0 <= length;
    requires length <= dst_capacity;
    requires length <= src_capacity;
    requires 1 <= dst_capacity;
    requires 1 <= src_capacity;
    requires (length as uint32) <= 1073741823u32;
    requires (dst_capacity as uint32) <= 1073741823u32;
    requires (src_capacity as uint32) <= 1073741823u32;
    owns uninitialized(dst[0..dst_capacity]);
    views src[0..src_capacity];
    requires separate(memory(dst[0..dst_capacity]), memory(src[0..src_capacity]));
    ensures result == length;
    ensures forall (k: int32) {
        0 <= k and k < length implies src[k] == old(src[k])
    };
    ensures forall (k: int32) {
        0 <= k and k < length implies dst[k] == old(src[k])
    };
} by {
    step();
    step();
    loop {
        decreases length - i;
        invariant forall (k: int32) { 0 <= k and k < length implies src[k] == old(src[k]) };
        invariant 0 <= i;
        invariant i <= length;
        invariant forall (k: int32) { 0 <= k and k < i implies dst[k] == old(src[k]) };
        owns dst[0..length];
        initialize by {
            have forall (k: int32) { 0 <= k and k < length implies src[k] == old(src[k]) } by {
                intro(); intro(); normalize();
            }
            have 0 <= i;
            have i <= length;
            have forall (k: int32) { 0 <= k and k < i implies dst[k] == old(src[k]) } by {
                intro();
                intro();
                extract(0 <= k);
                extract(k < i);
                contradiction(0 <= k);
            }
        }
        preserve by {
            step();
            step();
            have forall (k: int32) { 0 <= k and k < length implies src[k] == old(src[k]) } by {
                intro();
                intro();
                instantiate(forall (k: int32) { at(region(3).entry, 0) <= at(region(3).entry, k) and at(region(3).entry, k) < at(region(3).entry, length) implies at(region(3).entry, src[k]) == old(src[k]) }, k) using {
                    0 <= k and k < length;
                    at(region(3).entry, i) < at(region(3).entry, length);
                    at(function.entry, 0) <= at(function.entry, length);
                    at(function.entry, 0) <= at(function.entry, dst_capacity);
                    at(function.entry, 0) <= at(function.entry, src_capacity);
                    at(region(3).entry, 0) <= at(region(3).entry, i);
                    at(function.entry, 1) <= at(function.entry, dst_capacity);
                    at(function.entry, 1) <= at(function.entry, src_capacity);
                    at(function.entry, length) <= at(function.entry, 1073741823);
                    at(function.entry, length) <= at(function.entry, dst_capacity);
                    at(function.entry, length) <= at(function.entry, src_capacity);
                    at(function.entry, dst_capacity) <= at(function.entry, 1073741823);
                    at(function.entry, src_capacity) <= at(function.entry, 1073741823);
                    at(region(3).entry, i) <= at(region(3).entry, length);
                    at(function.entry, (length as uint32)) <= at(function.entry, 1073741823u32);
                    at(function.entry, (dst_capacity as uint32)) <= at(function.entry, 1073741823u32);
                    at(function.entry, (src_capacity as uint32)) <= at(function.entry, 1073741823u32);
                    little_endian();
                    at(function.entry, viewable((src as (int32 *))[0..src_capacity]));
                    at(function.entry, viewable((dst as (int32 *))[0..dst_capacity]));
                    at(function.entry, separate(memory(dst[0..dst_capacity]), memory(src[0..src_capacity])));
                    forall (k: int32) { at(region(3).entry, 0) <= at(region(3).entry, k) and at(region(3).entry,
                        k) < at(region(3).entry, i) implies at(region(3).entry, dst[k]) == old(src[k]) };
                };
                have at(region(3).entry, src[k]) == src[k] by {
                    transport(at(region(3).entry, src[k]) == at(region(3).entry, src[k]), at(region(3).entry, src[k]) == src[k]) using {
                        at(region(3).entry, src[k]) == at(region(3).entry, src[k]);
                        0 <= k and k < length;
                        at(region(3).entry, i) < at(region(3).entry, length);
                        at(function.entry, 0) <= at(function.entry, length);
                        at(function.entry, 0) <= at(function.entry, dst_capacity);
                        at(function.entry, 0) <= at(function.entry, src_capacity);
                        at(region(3).entry, 0) <= at(region(3).entry, i);
                        at(function.entry, 1) <= at(function.entry, dst_capacity);
                        at(function.entry, 1) <= at(function.entry, src_capacity);
                        at(function.entry, length) <= at(function.entry, 1073741823);
                        at(function.entry, length) <= at(function.entry, dst_capacity);
                        at(function.entry, length) <= at(function.entry, src_capacity);
                        at(function.entry, dst_capacity) <= at(function.entry, 1073741823);
                        at(function.entry, src_capacity) <= at(function.entry, 1073741823);
                        at(region(3).entry, i) <= at(region(3).entry, length);
                        at(function.entry, (length as uint32)) <= at(function.entry, 1073741823u32);
                        at(function.entry, (dst_capacity as uint32)) <= at(function.entry, 1073741823u32);
                        at(function.entry, (src_capacity as uint32)) <= at(function.entry, 1073741823u32);
                        little_endian();
                        at(function.entry, viewable((src as (int32 *))[0..src_capacity]));
                        at(function.entry, viewable((dst as (int32 *))[0..dst_capacity]));
                        at(function.entry, separate(memory(dst[0..dst_capacity]),
                            memory(src[0..src_capacity])));
                        forall (k: int32) { at(region(3).entry, 0) <= at(region(3).entry, k) and
                            at(region(3).entry, k) < at(region(3).entry, i) implies at(region(3).entry, dst[k])
                            == old(src[k]) };
                    };
                }
                have src[k] == at(region(3).entry, src[k]) by {
                    rewrite(at(region(3).entry, src[k]) == src[k]);
                    normalize();
                }
                rewrite(src[k] == at(region(3).entry, src[k]));
                assumption();
            }
            have 0 <= i by {
                arithmetic_certificate signed_int32 {
                    premise 0: (at(region(3).entry, 0) as int32) <= (at(region(3).entry, i) as int32) =>
                        (at(region(3).entry, 0) as int32) <= (at(region(3).entry, i) as int32);
                    premise 1: (at(region(3).entry, i) as int32) < (at(region(3).entry, length) as int32) =>
                        (at(region(3).entry, i) as int32) < (at(region(3).entry, length) as int32);
                    int32_range => to_integer((length as int32)) <= to_integer((2147483647 as int32));
                    add 1, 2 => (to_integer((at(region(3).entry, i) as int32)) + to_integer((length as int32)))
                        < (to_integer((at(region(3).entry, length) as int32)) + to_integer((2147483647 as
                        int32)));
                    interval_from_affine 0 (at(region(3).entry, i)) (0) (2147483647);
                    interval_from_affine 3 (at(region(3).entry, i)) (-2147483648) (2147483646);
                    interval_intersect 4, 5 (0) (2147483646);
                    interval_atom (1) (1) (1);
                    interval_add_bounded 6, 7 (1) (2147483647);
                    trivial => -1 <= 0;
                    add 0, 9 => (to_integer((at(region(3).entry, 0) as int32)) + -1) <=
                        (to_integer((at(region(3).entry, i) as int32)) + 0);
                    affine_conclusion 10 8 => (0 as int32) <= (i as int32);
                    conclusion 11;
                }
            }
            have i <= length by {
                arithmetic_certificate signed_int32 {
                    premise 0: (at(region(3).entry, i) as int32) < (at(region(3).entry, length) as int32) =>
                        (at(region(3).entry, i) as int32) < (at(region(3).entry, length) as int32);
                    int32_range => to_integer((length as int32)) <= to_integer((2147483647 as int32));
                    add 0, 1 => (to_integer((at(region(3).entry, i) as int32)) + to_integer((length as int32)))
                        < (to_integer((at(region(3).entry, length) as int32)) + to_integer((2147483647 as
                        int32)));
                    interval_from_affine 2 (at(region(3).entry, i)) (-2147483648) (2147483646);
                    interval_atom (1) (1) (1);
                    interval_add_bounded 3, 4 (-2147483647) (2147483647);
                    affine_conclusion 0 5 => (i as int32) <= (length as int32);
                    conclusion 6;
                }
            }
            have forall (k: int32) { 0 <= k and k < i implies dst[k] == old(src[k]) } by {
                intro();
                intro();
                extract(0 <= k);
                extract(k < i);
                if at(region(4).entry, k) < at(region(4).entry, (i as int32)) {
                    have at(region(4).entry, k) != at(region(4).entry, (i as int32)) by {
                        have at(region(4).entry, k) < at(region(4).entry, (i as int32)) by {
                            assumption();
                        }
                        intro();
                        arithmetic_certificate {
                            premise 0: at(region(4).entry, k) < at(region(4).entry, (i as int32)) =>
                                at(region(4).entry, k) < at(region(4).entry, (i as int32));
                            premise 1: at(region(4).entry, k) == at(region(4).entry, (i as int32)) =>
                                at(region(4).entry, k) == at(region(4).entry, (i as int32));
                            less_equal_from_equal 1 reverse => at(region(4).entry, to_integer(((i as int32) as
                                int32))) <= at(region(4).entry, to_integer((k as int32)));
                            add 0, 2 => (at(region(4).entry, to_integer((k as int32))) + at(region(4).entry,
                                to_integer(((i as int32) as int32)))) < (at(region(4).entry, to_integer(((i as
                                int32) as int32))) + at(region(4).entry, to_integer((k as int32))));
                            trivial => -1 <= 0;
                            equal_from_bounds 3, 4 => false == true;
                            conclusion 5;
                        }
                    }
                    instantiate(forall (k: int32) { at(region(3).entry, 0) <= at(region(3).entry, k) and at(region(3).entry, k) < at(region(3).entry, length) implies at(region(3).entry, src[k]) == old(src[k]) }, 0) using {
                        at(region(3).entry, i) < at(region(3).entry, length);
                        at(region(4).entry, k) < at(region(4).entry, (i as int32));
                        k < i;
                        0 <= length;
                        0 <= dst_capacity;
                        0 <= src_capacity;
                        at(region(3).entry, 0) <= at(region(3).entry, i);
                        0 <= k;
                        0 <= i;
                        1 <= dst_capacity;
                        1 <= src_capacity;
                        length <= 1073741823;
                        length <= dst_capacity;
                        length <= src_capacity;
                        dst_capacity <= 1073741823;
                        src_capacity <= 1073741823;
                        at(region(3).entry, i) <= at(region(3).entry, length);
                        i <= length;
                        at(region(4).entry, k) != at(region(4).entry, (i as int32));
                        (length as uint32) <= 1073741823u32;
                        (dst_capacity as uint32) <= 1073741823u32;
                        (src_capacity as uint32) <= 1073741823u32;
                    };
                    transport(at(region(3).entry, src[0]) == old(src[0]), dst[k] == old(src[k])) using {
                        at(region(3).entry, src[0]) == old(src[0]);
                        at(region(4).entry, k) < at(region(4).entry, (i as int32));
                        0 <= k;
                        forall (k: int32) { at(region(3).entry, 0) <= at(region(3).entry, k) and
                            at(region(3).entry, k) < at(region(3).entry, i) implies at(region(3).entry, dst[k])
                            == old(src[k]) };
                    };
                } else {
                    have at(region(4).entry, k) == at(region(4).entry, (i as int32)) by {
                        have at(region(4).entry, k) <= at(region(4).entry, (i as int32)) by {
                            arithmetic_certificate signed_int32 {
                                premise 0: (at(region(3).entry, i) as int32) < (at(region(3).entry, length) as
                                    int32) => (at(region(3).entry, i) as int32) < (at(region(3).entry, length)
                                    as int32);
                                premise 1: (k as int32) < (i as int32) => (k as int32) < (i as int32);
                                premise 2: (at(region(3).entry, 0) as int32) <= (at(region(3).entry, i) as
                                    int32) => (at(region(3).entry, 0) as int32) <= (at(region(3).entry, i) as
                                    int32);
                                premise 3: (at(function.entry, length) as int32) <= (at(function.entry,
                                    dst_capacity) as int32) => (at(function.entry, length) as int32) <=
                                    (at(function.entry, dst_capacity) as int32);
                                premise 4: (at(function.entry, dst_capacity) as int32) <= (at(function.entry,
                                    1073741823) as int32) => (at(function.entry, dst_capacity) as int32) <=
                                    (at(function.entry, 1073741823) as int32);
                                premise 5: (at(function.entry, i) as int32) <= (at(function.entry, length) as
                                    int32) => (at(function.entry, i) as int32) <= (at(function.entry, length) as
                                    int32);
                                add 3, 4 => (to_integer((at(function.entry, length) as int32)) +
                                    to_integer((at(function.entry, dst_capacity) as int32))) <=
                                    (to_integer((at(function.entry, dst_capacity) as int32)) +
                                    to_integer((at(function.entry, 1073741823) as int32)));
                                add 0, 6 => (to_integer((at(region(3).entry, i) as int32)) +
                                    (to_integer((at(function.entry, length) as int32)) +
                                    to_integer((at(function.entry, dst_capacity) as int32)))) <
                                    (to_integer((at(region(3).entry, length) as int32)) +
                                    (to_integer((at(function.entry, dst_capacity) as int32)) +
                                    to_integer((at(function.entry, 1073741823) as int32))));
                                interval_from_affine 2 (at(region(3).entry, i)) (0) (2147483647);
                                interval_from_affine 7 (at(region(3).entry, i)) (-2147483648) (1073741822);
                                interval_intersect 8, 9 (0) (1073741822);
                                interval_atom (1) (1) (1);
                                interval_add_bounded 10, 11 (1) (1073741823);
                                affine_premise 1 12 12 => to_integer((k as int32)) < to_integer((i as int32));
                                conclusion 13;
                            }
                        }
                        arithmetic_certificate {
                            premise 0: at(region(4).entry, k) <= at(region(4).entry, (i as int32)) =>
                                at(region(4).entry, k) <= at(region(4).entry, (i as int32));
                            premise 1: not k < at(region(3).entry, i) => not k < at(region(3).entry, i);
                            equal_from_bounds 0, 1 => at(region(4).entry, k) == at(region(4).entry, (i as
                                int32));
                            conclusion 2;
                        }
                    }
                    rewrite(at(region(4).entry, k) == at(region(4).entry, (i as int32)));
                    instantiate(forall (k: int32) { 0 <= k and k < length implies src[k] == old(src[k]) }, k) using {
                        at(region(3).entry, i) < at(region(3).entry, length);
                        not k < at(region(3).entry, i);
                        k < i;
                        at(function.entry, 0) <= at(function.entry, length);
                        at(function.entry, 0) <= at(function.entry, dst_capacity);
                        at(function.entry, 0) <= at(function.entry, src_capacity);
                        at(region(3).entry, 0) <= at(region(3).entry, i);
                        0 <= k;
                        at(function.entry, 0) <= at(function.entry, i);
                        at(function.entry, 1) <= at(function.entry, dst_capacity);
                        at(function.entry, 1) <= at(function.entry, src_capacity);
                        at(function.entry, length) <= at(function.entry, 1073741823);
                        at(function.entry, length) <= at(function.entry, dst_capacity);
                        at(function.entry, length) <= at(function.entry, src_capacity);
                        at(function.entry, dst_capacity) <= at(function.entry, 1073741823);
                        at(function.entry, src_capacity) <= at(function.entry, 1073741823);
                        at(region(3).entry, i) <= at(region(3).entry, length);
                        at(function.entry, i) <= at(function.entry, length);
                        at(region(4).entry, k) == at(region(4).entry, (i as int32));
                        at(function.entry, (length as uint32)) <= at(function.entry, 1073741823u32);
                        at(function.entry, (dst_capacity as uint32)) <= at(function.entry, 1073741823u32);
                        at(function.entry, (src_capacity as uint32)) <= at(function.entry, 1073741823u32);
                        little_endian();
                        at(function.entry, viewable((src as (int32 *))[0..src_capacity]));
                        at(function.entry, viewable((dst as (int32 *))[0..dst_capacity]));
                        at(function.entry, separate(memory(dst[0..dst_capacity]),
                            memory(src[0..src_capacity])));
                        forall (k: int32) { at(region(3).entry, 0) <= at(region(3).entry, k) and
                            at(region(3).entry, k) < at(region(3).entry, length) implies at(region(3).entry,
                            src[k]) == old(src[k]) };
                        forall (k: int32) { at(region(3).entry, 0) <= at(region(3).entry, k) and
                            at(region(3).entry, k) < at(region(3).entry, i) implies at(region(3).entry, dst[k])
                            == old(src[k]) };
                    };
                    transport(src[k] == old(src[k]), at(region(3).entry, src[i]) == old(src[at(region(3).entry, i)])) using {
                        src[k] == old(src[k]);
                        at(region(3).entry, i) < at(region(3).entry, length);
                        not k < at(region(3).entry, i);
                        k < i;
                        at(function.entry, 0) <= at(function.entry, length);
                        at(function.entry, 0) <= at(function.entry, dst_capacity);
                        at(function.entry, 0) <= at(function.entry, src_capacity);
                        at(region(3).entry, 0) <= at(region(3).entry, i);
                        0 <= k;
                        at(function.entry, 0) <= at(function.entry, i);
                        at(function.entry, 1) <= at(function.entry, dst_capacity);
                        at(function.entry, 1) <= at(function.entry, src_capacity);
                        at(function.entry, length) <= at(function.entry, 1073741823);
                        at(function.entry, length) <= at(function.entry, dst_capacity);
                        at(function.entry, length) <= at(function.entry, src_capacity);
                        at(function.entry, dst_capacity) <= at(function.entry, 1073741823);
                        at(function.entry, src_capacity) <= at(function.entry, 1073741823);
                        at(region(3).entry, i) <= at(region(3).entry, length);
                        at(function.entry, i) <= at(function.entry, length);
                        at(region(4).entry, k) == at(region(4).entry, (i as int32));
                        at(function.entry, (length as uint32)) <= at(function.entry, 1073741823u32);
                        at(function.entry, (dst_capacity as uint32)) <= at(function.entry, 1073741823u32);
                        at(function.entry, (src_capacity as uint32)) <= at(function.entry, 1073741823u32);
                        little_endian();
                        at(function.entry, viewable((src as (int32 *))[0..src_capacity]));
                        at(function.entry, viewable((dst as (int32 *))[0..dst_capacity]));
                        at(function.entry, separate(memory(dst[0..dst_capacity]),
                            memory(src[0..src_capacity])));
                        forall (k: int32) { at(region(3).entry, 0) <= at(region(3).entry, k) and
                            at(region(3).entry, k) < at(region(3).entry, length) implies at(region(3).entry,
                            src[k]) == old(src[k]) };
                        forall (k: int32) { at(region(3).entry, 0) <= at(region(3).entry, k) and
                            at(region(3).entry, k) < at(region(3).entry, i) implies at(region(3).entry, dst[k])
                            == old(src[k]) };
                    };
                }
            }
            have forall (k: int32) { 0 <= k and k < length implies src[k] == old(src[k]) } implies 0 <= i by {
                intro();
                assumption();
            }
            have forall (k: int32) { 0 <= k and k < length implies src[k] == old(src[k]) } implies 0 <= i implies i <= length by {
                intro();
                intro();
                assumption();
            }
            have forall (k: int32) { 0 <= k and k < length implies src[k] == old(src[k]) } implies 0 <= i implies i <= length implies forall (k: int32) { 0 <= k and k < i implies dst[k] == old(src[k]) } by {
                intro();
                intro();
                intro();
                assumption();
            }
            have (let integer_value: Integer = 0; integer_value) <= (to_integer((length as int32)) - to_integer((i as int32))) by {
                arithmetic_certificate {
                    negated_goal => (to_integer((length as int32)) - to_integer((i as int32))) < (let
                        integer_value: Integer = 0; integer_value);
                    premise 0: to_integer((i as int32)) <= to_integer((length as int32)) => to_integer((i as
                        int32)) <= to_integer((length as int32));
                    add 0, 1 => ((to_integer((length as int32)) - to_integer((i as int32))) + to_integer((i as
                        int32))) < ((let integer_value: Integer = 0; integer_value) + to_integer((length as
                        int32)));
                    conclusion 2;
                }
            }
            have (let integer_value: Integer = (to_integer((length as int32)) - to_integer((i as int32))); integer_value) < (to_integer((length as int32)) - to_integer(at(region(3).entry, (i as int32)))) by {
                have -2147483648 <= (to_integer(at(region(3).entry, (i as int32))) + 1) by {
                    arithmetic_certificate {
                        negated_goal => (to_integer(at(region(3).entry, (i as int32))) + 1) < -2147483648;
                        premise 0: 0 <= to_integer(at(region(3).entry, (i as int32))) => 0 <=
                            to_integer(at(region(3).entry, (i as int32)));
                        add 0, 1 => (to_integer(at(region(3).entry, (i as int32))) + 1 + 0) < (-2147483648 +
                            to_integer(at(region(3).entry, (i as int32))));
                        conclusion 2;
                    }
                }
                have (to_integer(at(region(3).entry, (i as int32))) + 1) <= 2147483647 by {
                    arithmetic_certificate {
                        negated_goal => 2147483647 < (to_integer(at(region(3).entry, (i as int32))) + 1);
                        premise 0: to_integer(at(region(3).entry, (i as int32))) <
                            to_integer(at(region(3).entry, length)) => to_integer(at(region(3).entry, (i as
                            int32))) < to_integer(at(region(3).entry, length));
                        premise 1: to_integer(at(region(3).entry, length)) <= 1073741823 =>
                            to_integer(at(region(3).entry, length)) <= 1073741823;
                        add 0, 1 => (2147483647 + 1 + (to_integer(at(region(3).entry, (i as int32))) + 1)) <=
                            (to_integer(at(region(3).entry, (i as int32))) + 1 + to_integer(at(region(3).entry,
                            length)));
                        add 3, 2 => (2147483647 + 1 + (to_integer(at(region(3).entry, (i as int32))) + 1) +
                            to_integer(at(region(3).entry, length))) <= (to_integer(at(region(3).entry, (i as
                            int32))) + 1 + to_integer(at(region(3).entry, length)) + 1073741823);
                        conclusion 4;
                    }
                }
                have to_integer((i as int32)) == (to_integer(at(region(3).entry, (i as int32))) + 1) by {
                    arithmetic_certificate rules {
                        premise 0: -2147483648 <= (to_integer(at(region(3).entry, (i as int32))) + 1) =>
                            -2147483648 <= (to_integer(at(region(3).entry, (i as int32))) + 1);
                        premise 1: (to_integer(at(region(3).entry, (i as int32))) + 1) <= 2147483647 =>
                            (to_integer(at(region(3).entry, (i as int32))) + 1) <= 2147483647;
                        integer_operation_identity bounds [0, 1] => to_integer((i as int32)) ==
                            (to_integer(at(region(3).entry, (i as int32))) + 1);
                        conclusion 0;
                    }
                }
                arithmetic_certificate {
                    negated_goal => (to_integer((length as int32)) - to_integer(at(region(3).entry, (i as
                        int32)))) <= (let integer_value: Integer = (to_integer((length as int32)) -
                        to_integer((i as int32))); integer_value);
                    premise 0: to_integer((i as int32)) == (to_integer(at(region(3).entry, (i as int32))) + 1)
                        => to_integer((i as int32)) == (to_integer(at(region(3).entry, (i as int32))) + 1);
                    less_equal_from_equal 1 reverse => (to_integer(at(region(3).entry, (i as int32))) + 1) <=
                        to_integer((i as int32));
                    add 0, 2 => ((to_integer((length as int32)) - to_integer(at(region(3).entry, (i as int32))))
                        + (to_integer(at(region(3).entry, (i as int32))) + 1)) <= ((let integer_value: Integer =
                        (to_integer((length as int32)) - to_integer((i as int32))); integer_value) +
                        to_integer((i as int32)));
                    conclusion 3;
                }
            }
        }
    }
    have i == length;
    have forall (k: int32) { 0 <= k and k < length implies dst[k] == old(src[k]) } by {
        intro();
        intro();
        instantiate(forall (k: int32) { at(loop(0).exit, 0) <= at(loop(0).exit, k) and at(loop(0).exit, k) < at(loop(0).exit, i) implies at(loop(0).exit, dst[k]) == old(src[k]) }, k) using {
            0 <= k and k < length;
            i == length;
        };
        assumption();
    }
    have forall (k: int32) { 0 <= k and k < length implies src[k] == old(src[k]) } by {
        intro(); intro();
        instantiate(at(loop(0).exit, forall (k: int32) { 0 <= k and k < length implies src[k] == old(src[k]) }), k) using { 0 <= k and k < length; };
        assumption();
    }
    step();
    have forall (k: int32) { 0 <= k and k < length implies dst[k] == old(src[k]) } by {
        assumption();
    }
    assumption();
    assumption();
    assumption();
    assumption();
}

int32 vector_grow(struct vector* owner) {
    let entry_length = old(owner->len);
    let entry_capacity = old(owner->cap);

    requires owner->cap <= 536870910;
    owns allocated_vector(owner);
    ensures result == 0 or result == 1;
    ensures owner->len == entry_length;
    ensures result == 0 implies owner->cap == entry_capacity;
    ensures result == 0 implies owner->data == old(owner->data);
    ensures result == 1 implies owner->cap == entry_capacity + 1;
    ensures forall (k: int32) {
        0 <= k and k < entry_length implies
            owner->data[k] == old(owner->data[k])
    };
} by {
    unfold(allocated_vector(owner));
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    have 0 <= old_capacity by {
        rewrite(old_capacity == owner->cap);
        have 0 <= owner->cap;
        assumption();
    }
    have (old_capacity as uint32) <= 1073741823u32 by {
        rewrite(old_capacity == owner->cap);
        solve() using {
            1 <= owner->cap;
            owner->cap <= 536870910;
        };
    }
    if new_data == 0 {
        step();
        step();
        have forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) } by {
            intro();
            intro();
            extract(0 <= k);
            extract(k < old(owner->len));
            transport(old(owner->data[k]) == old(owner->data[k]), owner->data[k] == old(owner->data[k])) using {
                0 <= k;
                k < old(owner->len);
            };
            assumption();
        }
        fold(allocated_vector(owner));
        have result == 0;
        have result == 0 implies owner->cap == old(owner->cap);
        have result == 0 implies owner->data == old(owner->data);
        have result == 1 implies owner->cap == (old(owner->cap) + 1);
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
    } else {
        have 1 <= new_capacity by { solve() using { 1 <= old_capacity; old_capacity <= 536870911; }; }
        have new_capacity <= 536870912 by { solve() using { 1 <= old_capacity; old_capacity <= 536870911; }; }
        have (new_capacity as uint32) <= 1073741823u32 by {
            solve() using { 1 <= new_capacity; new_capacity <= 536870912; };
        }
        have (owner->len as uint32) <= 1073741823u32 by {
            solve() using { 0 <= owner->len; owner->len <= owner->cap; owner->cap <= 536870910; };
        }
        step();
        step();
        step();
        step();
        step();
        step();
        step();
        have owner->cap == at(region(9).entry, new_capacity);
        have owner->data == at(region(13).entry, new_data);
        have forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) } by {
            intro();
            intro();
            instantiate(forall (__click_q0: int32) { at(region(13).entry, 0) <= at(region(13).entry, __click_q0) and at(region(13).entry, __click_q0) < at(region(13).entry, owner->len) implies at(region(13).entry, new_data[__click_q0]) == at(region(13).entry, old_data[__click_q0]) }, k) using {
                0 <= k and k < old(owner->len);
                owner->data == owner->data;
            };
            have &owner->data[k] == at(region(13).entry, &new_data[k]) by {
                normalize() using { owner->data == at(region(13).entry, new_data); };
            }
            have separate(memory(owner->data[k]), memory(old(owner->data)[0..old(owner->cap)]));
            transport(at(region(13).entry, new_data[k]) == at(region(13).entry, old_data[k]), owner->data[k] == old(owner->data[k])) using {
                &owner->data[k] == at(region(13).entry, &new_data[k]);
                separate(memory(owner->data[k]), memory(old(owner->data)[0..old(owner->cap)]));
                at(region(13).entry, new_data[k]) == at(region(13).entry, old_data[k]);
                0 <= k and k < old(owner->len);
                owner->data == owner->data;
            };
        }
        fold(allocated_vector(owner));
        have result == 0 implies owner->cap == old(owner->cap);
        have result == 0 implies owner->data == old(owner->data);
        have result == 1 implies to_integer(owner->cap) == (to_integer(old(owner->cap)) + 1) by {
            have 0 == 0 implies (let integer_value: Integer = to_integer(at(region(7).exit, (new_capacity as int32))); integer_value) == (to_integer(at(region(5).exit, (old_capacity as int32))) + 1) by {
                intro();
                if at(function.entry, owner->cap < (536870910 as int32)) {
                    have at(function.entry, owner->cap != (536870910 as int32)) by {
                        if at(function.entry, owner->cap) < (at(function.entry, 1073741823) as int32) {
                            have at(function.entry, owner->cap) != (at(function.entry, 1073741823) as int32) by {
                                have at(function.entry, owner->cap) < (at(function.entry, 1073741823) as int32) by {
                                    assumption();
                                }
                                intro();
                                arithmetic_certificate {
                                    premise 0: at(function.entry, owner->cap) < (at(function.entry,
                                        1073741823) as int32) => at(function.entry, owner->cap) <
                                        (at(function.entry, 1073741823) as int32);
                                    premise 1: at(function.entry, owner->cap) == (at(function.entry,
                                        1073741823) as int32) => at(function.entry, owner->cap) ==
                                        (at(function.entry, 1073741823) as int32);
                                    less_equal_from_equal 1 reverse => to_integer(((at(function.entry,
                                        1073741823) as int32) as int32)) <= at(function.entry,
                                        to_integer((owner->cap as int32)));
                                    add 0, 2 => (at(function.entry, to_integer((owner->cap as int32))) +
                                        to_integer(((at(function.entry, 1073741823) as int32) as int32))) <
                                        (to_integer(((at(function.entry, 1073741823) as int32) as int32)) +
                                        at(function.entry, to_integer((owner->cap as int32))));
                                    trivial => -1 <= 0;
                                    equal_from_bounds 3, 4 => false == true;
                                    conclusion 5;
                                }
                            }
                            arithmetic_certificate signed_int32 {
                                premise 0: (at(function.entry, owner->cap) as int32) < (at(function.entry,
                                    536870910) as int32) => (at(function.entry, owner->cap) as int32) <
                                    (at(function.entry, 536870910) as int32);
                                premise 1: (at(function.entry, 1) as int32) <= (at(function.entry,
                                    owner->cap) as int32) => (at(function.entry, 1) as int32) <=
                                    (at(function.entry, owner->cap) as int32);
                                interval_from_affine 1 (at(function.entry, owner->cap)) (1) (2147483647);
                                interval_from_affine 0 (at(function.entry, owner->cap)) (-2147483648)
                                    (536870909);
                                interval_intersect 2, 3 (1) (536870909);
                                interval_atom (536870910) (536870910) (536870910);
                                interval_compare 4, 5 ne => at(function.entry, owner->cap != (536870910 as
                                    int32));
                                conclusion 6;
                            }
                        } else {
                            have at(function.entry, owner->cap) == (at(function.entry, 1073741823) as int32) by {
                                have at(function.entry, owner->cap) <= (at(function.entry, 1073741823) as int32) by {
                                    assumption();
                                }
                                arithmetic_certificate {
                                    premise 0: at(function.entry, owner->cap) <= (at(function.entry,
                                        1073741823) as int32) => at(function.entry, owner->cap) <=
                                        (at(function.entry, 1073741823) as int32);
                                    premise 1: not at(function.entry, owner->cap) < at(function.entry,
                                        1073741823) => not at(function.entry, owner->cap) <
                                        at(function.entry, 1073741823);
                                    equal_from_bounds 0, 1 => at(function.entry, owner->cap) ==
                                        (at(function.entry, 1073741823) as int32);
                                    conclusion 2;
                                }
                            }
                            rewrite(at(function.entry, owner->cap) == (at(function.entry, 1073741823) as int32));
                            normalize();
                        }
                    }
                    have -2147483648 <= (to_integer(at(region(5).exit, (old_capacity as int32))) + 1) by {
                        arithmetic_certificate {
                            negated_goal => (to_integer(at(region(5).exit, (old_capacity as int32))) + 1) <
                                -2147483648;
                            premise 0: 0 <= to_integer(at(region(5).exit, (old_capacity as int32))) => 0 <=
                                to_integer(at(region(5).exit, (old_capacity as int32)));
                            add 0, 1 => (to_integer(at(region(5).exit, (old_capacity as int32))) + 1 + 0) <
                                (-2147483648 + to_integer(at(region(5).exit, (old_capacity as int32))));
                            conclusion 2;
                        }
                    }
                    have (to_integer(at(region(5).exit, (old_capacity as int32))) + 1) <= 2147483647 by {
                        arithmetic_certificate {
                            negated_goal => 2147483647 < (to_integer(at(region(5).exit, (old_capacity as
                                int32))) + 1);
                            premise 0: to_integer(at(region(5).exit, (old_capacity as int32))) < 536870910
                                => to_integer(at(region(5).exit, (old_capacity as int32))) < 536870910;
                            add 0, 1 => (2147483647 + 1 + (to_integer(at(region(5).exit, (old_capacity as
                                int32))) + 1)) <= (to_integer(at(region(5).exit, (old_capacity as int32))) +
                                1 + 536870910);
                            conclusion 2;
                        }
                    }
                    have to_integer((let integer_value: Integer = to_integer(at(region(7).exit, (new_capacity as int32))); integer_value)) == (to_integer(at(region(5).exit, (old_capacity as int32))) + 1) by {
                        arithmetic_certificate rules {
                            premise 0: -2147483648 <= (to_integer(at(region(5).exit, (old_capacity as
                                int32))) + 1) => -2147483648 <= (to_integer(at(region(5).exit, (old_capacity
                                as int32))) + 1);
                            premise 1: (to_integer(at(region(5).exit, (old_capacity as int32))) + 1) <=
                                2147483647 => (to_integer(at(region(5).exit, (old_capacity as int32))) + 1)
                                <= 2147483647;
                            integer_operation_identity bounds [0, 1] => to_integer((let integer_value:
                                Integer = to_integer(at(region(7).exit, (new_capacity as int32)));
                                integer_value)) == (to_integer(at(region(5).exit, (old_capacity as int32)))
                                + 1);
                            conclusion 0;
                        }
                    }
                    assumption();
                } else {
                    have at(function.entry, owner->cap == (536870910 as int32)) by {
                        have at(function.entry, owner->cap <= (536870910 as int32)) by {
                            assumption();
                        }
                        arithmetic_certificate {
                            premise 0: at(function.entry, owner->cap <= (536870910 as int32)) =>
                                at(function.entry, owner->cap <= (536870910 as int32));
                            premise 1: not at(function.entry, owner->cap) < at(function.entry, 536870910) =>
                                not at(function.entry, owner->cap) < at(function.entry, 536870910);
                            equal_from_bounds 0, 1 => at(function.entry, owner->cap) == at(function.entry,
                                (536870910 as int32));
                            conclusion 2;
                        }
                    }
                    rewrite(at(function.entry, owner->cap == (536870910 as int32)));
                    normalize();
                }
            }
            assumption();
        }
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
    }
}

int32 vector_push(struct vector* owner, int32 value) {
    requires owner->len < owner->cap;
    owns vector_storage(owner);
    ensures result == old(owner->len) + 1;
    ensures owner->len == old(owner->len) + 1;
    ensures owner->data[old(owner->len)] == value;
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
    ensures forall (k: int32) {
        0 <= k and k < old(owner->len) implies
            owner->data[k] == old(owner->data[k])
    };
} by {
    unfold(vector_storage(owner));
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    have owner->data == old(owner->data) by {
        solve();
    }
    have owner->data[old(owner->len)] == value by {
        solve();
    }
    fold(vector_storage(owner));
    have forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < old(owner->len));
        transport(old(owner->data[k]) == old(owner->data[k]), owner->data[k] == old(owner->data[k])) using {
            at(region(5).entry, owner->len) <= at(region(5).entry, owner->cap);
            0 <= k;
            k < old(owner->len);
        };
        assumption();
    }
    solve();
}

int32 allocated_vector_push(struct vector* owner, int32 value) {
    requires owner->cap <= 536870910;
    owns allocated_vector(owner);
    ensures result == 0 or result == 1;
    ensures result == 0 implies owner->len == old(owner->len);
    ensures result == 0 implies owner->cap == old(owner->cap);
    ensures result == 0 implies owner->data == old(owner->data);
    ensures result == 1 implies owner->len == old(owner->len) + 1;
    ensures result == 1 implies owner->data[old(owner->len)] == value;
    ensures forall (k: int32) {
        0 <= k and k < old(owner->len) implies
            owner->data[k] == old(owner->data[k])
    };
    ensures old(owner->len) < old(owner->cap) implies result == 1;
    ensures old(owner->len) < old(owner->cap) implies
        owner->cap == old(owner->cap);
    ensures old(owner->len) < old(owner->cap) implies
        owner->data == old(owner->data);
} by {
    if owner->len == owner->cap {
        open(allocated_vector(owner)) {
            step();
            have separate(statement(0).footprint, memory(owner->data)) by { normalize() using {}; }
            have owner->data == at(statement(0).entry, owner->data) by {
                transport_certificate {
                    premise 0: separate(statement(0).footprint, memory(owner->data)) => separate(statement(0).footprint, memory(owner->data));
                    preserve 0 => owner->data == at(statement(0).entry, owner->data);
                    conclusion 1;
                }
            }
            step();
            have separate(statement(1).footprint, memory(owner->data)) by { normalize() using {}; }
            have owner->data == at(statement(1).entry, owner->data) by {
                transport_certificate {
                    premise 0: separate(statement(1).footprint, memory(owner->data)) => separate(statement(1).footprint, memory(owner->data));
                    preserve 0 => owner->data == at(statement(1).entry, owner->data);
                    conclusion 1;
                }
            }
            step();
        }
        mark before_grow;
        step();
        have c(grown) == 0 implies owner->data == at(before_grow, owner->data) by { assumption(); }
        if c(grown) == 0 {
            step();
            step();
            have not old(owner->len) < old(owner->cap) by {
                rewrite(at(function.entry, owner->len == owner->cap));
                normalize();
            }
            have result == 0 by {
                normalize();
            }
            have result == 0 or result == 1 by {
                assumption();
            }
            have result == 0 implies owner->len == old(owner->len) by {
                intro();
                transport(old(owner->len) == old(owner->len), owner->len == old(owner->len)) using {
                };
                assumption();
            }
            have result == 0 implies owner->cap == old(owner->cap) by {
                intro();
                extract(at(region(4).entry, owner->cap) == at(region(3).entry, owner->cap));
                assumption();
            }
            have result == 0 implies owner->data == old(owner->data) by {
                intro();
                extract(at(region(4).entry, owner->data) == at(region(3).entry, owner->data));
                assumption();
            }
            have result == 1 implies owner->len == (old(owner->len) + 1) by {
                intro();
                contradiction(result == 1);
            }
            have result == 1 implies owner->data[old(owner->len)] == value by {
                intro();
                contradiction(result == 1);
            }
            have forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) } by {
                assumption();
            }
            have old(owner->len) < old(owner->cap) implies result == 1 by {
                intro();
                contradiction(old(owner->len) < old(owner->cap));
            }
            have old(owner->len) < old(owner->cap) implies owner->cap == old(owner->cap) by {
                intro();
                contradiction(old(owner->len) < old(owner->cap));
            }
            have old(owner->len) < old(owner->cap) implies owner->data == old(owner->data) by {
                intro();
                contradiction(old(owner->len) < old(owner->cap));
            }
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
        } else {
            step();
            step();
            unfold(allocated_vector(owner));
            have c(grown) == 1 by {
                cases {
                    c(grown) == 0 => {
                        contradiction(c(grown) == 0);
                    }
                    c(grown) == 1 => {
                        assumption();
                    }
                }
            }
            have owner->len == old(owner->len) by {
                assumption();
            }
            have owner->cap == (old(owner->cap) + 1) by {
                extract(owner->cap == (old(owner->cap) + 1));
                assumption();
            }
            have owner->len < owner->cap;
            fold(vector_storage(owner));
            step();
            have at(region(8).exit, owner->data[at(region(8).entry, owner->len)]) == at(region(8).exit, value) by {
                assumption();
            }
            unfold(vector_storage(owner));
            have 0 <= owner->len by {
                assumption();
            }
            have owner->len <= owner->cap by {
                assumption();
            }
            have owner->cap == at(region(8).entry, owner->cap) by {
                assumption();
            }
            have 1 <= at(region(8).entry, owner->cap) by {
                assumption();
            }
            have at(region(8).entry, owner->cap) <= 536870911 by {
                assumption();
            }
            have 1 <= owner->cap by {
                rewrite(owner->cap == at(region(8).entry, owner->cap));
                assumption();
            }
            have owner->cap <= 536870911 by {
                rewrite(owner->cap == at(region(8).entry, owner->cap));
                assumption();
            }
            fold(allocated_vector(owner));
            step();
            have not old(owner->len) < old(owner->cap) by {
                rewrite(at(function.entry, owner->len == owner->cap));
                normalize();
            }
            have result == 0 or result == 1 by {
                have result == 1 by normalize();
                assumption();
            }
            have result == 0 implies owner->len == old(owner->len) by {
                solve();
            }
            have result == 0 implies owner->cap == old(owner->cap) by {
                solve();
            }
            have result == 0 implies owner->data == old(owner->data) by {
                solve();
            }
            have at(region(8).entry, owner->len) == old(owner->len) by {
                assumption();
            }
            have owner->len == (old(owner->len) + 1) by {
                rewrite(owner->len == (at(region(8).entry, owner->len) + 1));
                rewrite(at(region(8).entry, owner->len) == old(owner->len));
                normalize();
            }
            have result == 1 implies owner->len == (old(owner->len) + 1) by {
                intro();
                assumption();
            }
            have at(region(8).entry, owner->len) < at(region(8).entry, owner->cap) by {
                assumption();
            }
            have at(region(8).entry, owner->len) == old(owner->len) by {
                assumption();
            }
            have owner->cap == at(region(8).entry, owner->cap) by {
                assumption();
            }
            have old(owner->len) < owner->cap by {
                transport(at(region(8).entry, owner->len) < at(region(8).entry, owner->cap), old(owner->len) < owner->cap) using {
                    at(region(8).entry, owner->len) < at(region(8).entry, owner->cap);
                    at(region(8).entry, owner->len) == old(owner->len);
                    owner->cap == at(region(8).entry, owner->cap);
                };
                assumption();
            }
            have owner->data[old(owner->len)] == value by {
                rewrite(old(owner->len) == at(region(8).entry, owner->len));
                assumption();
            }
            have result == 1 implies owner->data[old(owner->len)] == value by {
                intro();
                assumption();
            }
            have forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) } by {
                intro();
                intro();
                extract(0 <= k);
                extract(k < old(owner->len));
                instantiate(forall (j: int32) { 0 <= j and j < old(owner->len) implies at(region(4).entry, owner->data[j]) == old(owner->data[j]) }, k);
                have k < at(region(8).entry, owner->len) by {
                    rewrite(at(region(8).entry, owner->len) == old(owner->len));
                    assumption();
                }
                instantiate(forall (j: int32) { 0 <= j and j < at(region(8).entry, owner->len) implies at(region(8).exit, owner->data[j]) == at(region(8).entry, owner->data[j]) }, k) using {
                    0 <= k;
                    k < at(region(8).entry, owner->len);
                };
                transport(at(region(8).exit, owner->data[k]) == at(region(8).entry, owner->data[k]), owner->data[k] == at(region(8).entry, owner->data[k])) using {
                    at(region(8).exit, owner->data[k]) == at(region(8).entry, owner->data[k]);
                    0 <= k;
                    k < at(region(8).entry, owner->len);
                };
                transport(at(region(4).entry, owner->data[k]) == old(owner->data[k]), at(region(8).entry, owner->data[k]) == old(owner->data[k])) using {
                    at(region(4).entry, owner->data[k]) == old(owner->data[k]);
                    0 <= k;
                    k < old(owner->len);
                };
                rewrite(owner->data[k] == at(region(8).entry, owner->data[k]));
                assumption();
            }
            have old(owner->len) < old(owner->cap) implies result == 1 by {
                intro();
                contradiction(old(owner->len) < old(owner->cap));
            }
            have old(owner->len) < old(owner->cap) implies owner->cap == old(owner->cap) by {
                intro();
                contradiction(old(owner->len) < old(owner->cap));
            }
            have old(owner->len) < old(owner->cap) implies owner->data == old(owner->data) by {
                intro();
                contradiction(old(owner->len) < old(owner->cap));
            }
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
        }
    } else {
        observe(allocated_vector(owner));
        have owner->len <= owner->cap by {
            assumption();
        }
        have not owner->len == owner->cap by {
            assumption();
        }
        have owner->len < owner->cap by {
            have owner->len < owner->cap;
            assumption();
        }
        have old(owner->len) < old(owner->cap) by {
            assumption();
        }
        step();
        step();
        step();
        step();
        unfold(allocated_vector(owner));
        fold(vector_storage(owner));
        step();
        unfold(vector_storage(owner));
        have 0 <= owner->len by {
            assumption();
        }
        have owner->len <= owner->cap by {
            assumption();
        }
        have 1 <= owner->cap by {
            rewrite(owner->cap == at(region(0).entry, owner->cap));
            assumption();
        }
        have owner->cap <= 536870911 by {
            rewrite(owner->cap == at(region(0).entry, owner->cap));
            assumption();
        }
        fold(allocated_vector(owner));
        step();
        have 0 == 0 by {
            normalize();
        }
        have at(region(0).entry, 0) <= at(region(0).entry, owner->len) by {
            assumption();
        }
        have at(region(0).entry, (owner->len + 1)) <= at(region(0).entry, owner->cap);
        have result == 1 by {
            normalize();
        }
        have result == 0 or result == 1 by {
            assumption();
        }
        have result == 0 implies owner->len == old(owner->len) by {
            solve();
        }
        have result == 0 implies owner->cap == old(owner->cap) by {
            solve();
        }
        have result == 0 implies owner->data == old(owner->data) by {
            solve();
        }
        have result == 1 implies owner->len == (old(owner->len) + 1) by {
            intro();
            assumption();
        }
        have owner->data[old(owner->len)] == value by {
            assumption();
        }
        have result == 1 implies owner->data[old(owner->len)] == value by {
            intro();
            assumption();
        }
        have forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) } by {
            assumption();
        }
        have owner->cap == old(owner->cap) by {
            assumption();
        }
        have owner->data == old(owner->data) by {
            assumption();
        }
        have old(owner->len) < old(owner->cap) implies result == 1 by {
            intro();
            assumption();
        }
        have old(owner->len) < old(owner->cap) implies owner->cap == old(owner->cap) by {
            intro();
            assumption();
        }
        have old(owner->len) < old(owner->cap) implies owner->data == old(owner->data) by {
            intro();
            assumption();
        }
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
    }
}

int32 vector_init(struct vector* owner, int32 data[], int32 capacity) {
    requires 1 <= capacity;
    requires capacity <= 1073741823;
    consumes *owner;
    consumes data[0..capacity];
    produces empty_vector(owner);
    ensures result == 0;
    ensures owner->len == 0;
    ensures owner->cap == capacity;
    ensures owner->data == data;
} by {
    step();
    step();
    step();
    step();
    fold(empty_vector(owner));
    have result == 0;
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
}

int32 vector_len(struct vector* owner) {
    views nonempty_vector(owner);

    ensures result == owner->len by {
        step();
        assumption();
    }
}

int32 vector_get(struct vector* owner, int32 index) {
    requires 0 <= index;
    requires index < owner->len;
    views nonempty_vector(owner);

    ensures result == owner->data[index];
    ensures result == old(owner->data[index]);
} by {
    step();
    step();
    step();
    assumption();
    assumption();
}

int32 vector_set(struct vector* owner, int32 index, int32 value) {
    requires 0 <= index;
    requires index < owner->len;
    owns nonempty_vector(owner);
    ensures result == value;
    ensures owner->data[index] == value;
    ensures owner->len == old(owner->len);
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
} by {
    unfold(nonempty_vector(owner));
    step();
    step();
    step();
    step();
    fold(nonempty_vector(owner));
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
}

int32 vector_fill(struct vector* owner, int32 value) {
    owns nonempty_vector(owner);
    ensures result == owner->len;
} by {
    unfold(nonempty_vector(owner));
    step();
    step();
    have i >= 0;
    have i <= owner->len;
    loop as fill_cells {
        decreases owner->len - i;
        invariant i >= 0 and i <= owner->len;
        invariant owner->len == old(owner->len);
        invariant owner->data == old(owner->data);
        owns owner->data[0..owner->len];
        initialize by solve();
        preserve by {
            mark before_fill;
            have i < owner->cap;
            have contains(memory(*owner), memory(owner->data)) by { normalize(); }
            have separate(memory(owner->data), memory(owner->data[i])) by {
                apply(selected_array_cell(memory(*owner), memory(owner->data),
                    owner->data, owner->cap, i)) using {
                    separate(memory(*owner), memory(owner->data[0..owner->cap]));
                    contains(memory(*owner), memory(owner->data));
                    0 <= i; i < owner->cap;
                };
            }
            step();
            have separate(loop(0).statement(0).footprint, memory(owner->data)) by {
                normalize() using {
                    at(before_fill, separate(memory(owner->data), memory(owner->data[i])));
                };
            }
            have owner->data == at(before_fill, owner->data) by {
                transport_certificate {
                    premise 0: separate(loop(0).statement(0).footprint, memory(owner->data))
                        => separate(loop(0).statement(0).footprint, memory(owner->data));
                    preserve 0 => owner->data == at(before_fill, owner->data);
                    conclusion 1;
                }
            }
            have owner->data == old(owner->data) by {
                normalize() using {
                    owner->data == at(before_fill, owner->data);
                    at(before_fill, owner->data) == old(owner->data);
                };
            }
            transport(at(before_fill, owner->len) == old(owner->len),
                      owner->len == old(owner->len)) using {
                at(before_fill, owner->len) == old(owner->len);
                at(before_fill, separate(memory(*owner), memory(owner->data[0..owner->cap])));
                0 <= at(before_fill, i);
                at(before_fill, i) < at(before_fill, owner->len);
                at(before_fill, owner->len) <= at(before_fill, owner->cap);
            };
            step();
            have 0 - at(region(3).entry, i) + owner->len - 1
                < 0 - at(region(3).entry, i) + owner->len;
        }
    }
    step();
    fold(nonempty_vector(owner));
    assumption();
    assumption();
}

int32 vector_replace_if(
    struct vector* owner,
    int32 index,
    int32 replacement,
    int32 replace
) {
    requires 0 <= index;
    requires index < owner->len;
    owns nonempty_vector(owner);

    ensures replace != 0 implies result == replacement;
} by {
    step();
    step();
    step();
    branch {
        step();
        have replace != 0 implies selected == replacement;
    } else {
        step();
        have replace != 0 implies selected == replacement by {
            intro();
            contradiction(not replace != 0);
        }
    }
    step();
    assumption();
    assumption();
}

int32 vector_clear(struct vector* owner) {
    consumes nonempty_vector(owner);
    produces empty_vector(owner);
    ensures result == 0;
    ensures owner->len == 0;
} by {
    unfold(nonempty_vector(owner));
    step();
    step();
    have owner->len == 0;
    have 1 <= at(region(0).entry, owner->cap);
    transport(at(region(0).entry, 1) <= at(region(0).entry, owner->cap), 1 <= owner->cap) using {
        at(region(0).entry, 1) <= at(region(0).entry, owner->cap);
    };
    assumption();
    fold(empty_vector(owner));
    assumption();
    assumption();
}

int32 vector_pipeline(
    struct vector* owner,
    int32 data[],
    int32 capacity,
    int32 first,
    int32 replacement
) {
    requires 1 <= capacity;
    requires capacity <= 1073741823;
    consumes *owner;
    consumes data[0..capacity];

    produces empty_vector(owner);
    ensures result == replacement;
} by {
    step();
    step();
    step();
    unfold(empty_vector(owner));
    fold(vector_storage(owner));
    step();
    unfold(vector_storage(owner));
    fold(nonempty_vector(owner));
    step();
    step();
    observe(nonempty_vector(owner));
    step();
    apply(int32_equality_transitive(observed, owner->data[0], replacement)) using {
        observed == owner->data[0];
        owner->data[0] == replacement;
    };
    step();
    step();
    assumption();
    assumption();
}
