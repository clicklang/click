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
        invariant 0 <= i;
        invariant i <= length;
        invariant forall (k: int32) { 0 <= k and k < i implies dst[k] == old(src[k]) };
        owns dst[0..length];
        initialize by {
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
            solve();
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
    step();
    have forall (k: int32) { 0 <= k and k < length implies src[k] == old(src[k]) } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < length);
        transport(old(src[k]) == old(src[k]), src[k] == old(src[k])) using {
            0 <= length;
            0 <= k;
            k < length;
            length <= dst_capacity;
            length <= src_capacity;
            1 <= dst_capacity;
            1 <= src_capacity;
            separate(memory(dst[0..dst_capacity]), memory(src[0..src_capacity]));
        };
        assumption();
    }
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
        step();
        step();
        step();
        step();
        step();
        step();
        step();
        have owner->cap == at(region(9).entry, new_capacity);
        have forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) } by solve();
        fold(allocated_vector(owner));
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
            step();
            step();
        }
        step();
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
            step();
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
