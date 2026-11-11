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

import click::integer;

resource preserved_cell(p: int32*) {
    field value: int32;
    owns *p;
    fact *p == value;
}

resource arena_initialized_storage(
    data: int32*,
    occupied: int32*,
    capacity: int32,
    initialized: int32
) {
    if initialized == 1 {
        owns allocation(data, capacity * 4);
        owns allocation(occupied, capacity * 4);
        fact 1 <= capacity;
        fact capacity <= 536870911;
    }
}

resource arena_cells(data: int32*, occupied: int32*, capacity: int32) {
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
}

resource arena_state(arena: struct arena*) {
    field live: int32;
    field capacity: int32;
    owns *arena;
    owns arena_initialized_storage(
        arena->data,
        arena->occupied,
        arena->capacity,
        1
    );
    owns arena_cells(arena->data, arena->occupied, arena->capacity);
    fact arena->capacity <= 536870911;
    fact arena->capacity == capacity;
    fact arena->live_regions == live;
    fact 0 <= live;
    fact separate(
        memory(arena->occupied[0..arena->capacity]),
        memory(arena->data[0..arena->capacity])
    );
    fact separate(
        memory(*arena),
        memory(arena->data[0..arena->capacity])
    );
    fact separate(
        memory(*arena),
        memory(arena->occupied[0..arena->capacity])
    );
}

resource arena_region(region: struct region*) {
    field start: int32;
    field end: int32;
    owns *region;
    owns region->arena->data[start..end];
    fact region->start == start;
    fact region->end == end;
    fact 0 <= start;
    fact start < end;
}

resource arena_window(
    data: int32*,
    occupied: int32*,
    capacity: int32,
    start: int32,
    end: int32
) {
    field next: int32;
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
    owns data[start..next];
    fact 0 <= start;
    fact start <= next;
    fact next <= end;
    fact end <= capacity;
    fact separate(memory(occupied[0..capacity]), memory(data[0..capacity]));
    fact forall (k: int32) {
        next <= k and k < end implies occupied[k] == 0
    };
    fact forall (k: int32) {
        start <= k and k < next implies occupied[k] == 1
    };
}

resource arena_clear_window(
    data: int32*,
    occupied: int32*,
    capacity: int32,
    start: int32,
    end: int32
) {
    field next: int32;
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
    owns data[next..end];
    fact 0 <= start;
    fact start <= next;
    fact next <= end;
    fact end <= capacity;
    fact separate(memory(occupied[0..capacity]), memory(data[0..capacity]));
    fact forall (k: int32) {
        start <= k and k < next implies occupied[k] == 0
    };
}

resource arena_scan(data: int32*, occupied: int32*, capacity: int32) {
    field lo: int32;
    field hi: int32;
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
    fact 0 <= lo;
    fact lo <= hi;
    fact hi <= capacity;
    fact forall (k: int32) {
        lo <= k and k < hi implies occupied[k] == 0
    };
}

spec enum ArenaInitOutcome {
    Failure,
    Success(int32, int32),
}

resource arena_init_outcome(arena: struct arena*) {
    field model: ArenaInitOutcome;
    match model {
        ArenaInitOutcome::Failure => {
            owns *arena;
        },
        ArenaInitOutcome::Success(live, capacity) => {
            owns state: arena_state(arena);
            fact state.live == live;
            fact state.capacity == capacity;
        },
    }
}

verifying "arena_init.c";

int32 arena_init(struct arena* arena, int32 capacity) {
    consumes *arena;
    produces outcome: arena_init_outcome(arena);

    ensures result == 0 or result == 1;
    ensures result == 0 implies outcome.model == ArenaInitOutcome::Failure;
    ensures result == 1 implies outcome.model == ArenaInitOutcome::Success(0, capacity);
    ensures forall (k: int32) {
        result == 1 and 0 <= k and k < arena->capacity implies
            arena->occupied[k] == 0
    };
} by {
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    branch {
        step();
        let outcome = fold(arena_init_outcome(arena), {
            model: ArenaInitOutcome::Failure
        });
        solve();
    } else {}
    branch {
        step();
        let outcome = fold(arena_init_outcome(arena), {
            model: ArenaInitOutcome::Failure
        });
        solve();
    } else {}
    step();
    branch {
        step();
        let outcome = fold(arena_init_outcome(arena), {
            model: ArenaInitOutcome::Failure
        });
        solve();
    } else {}
    step();
    branch {
        step();
        step();
        let outcome = fold(arena_init_outcome(arena), {
            model: ArenaInitOutcome::Failure
        });
        solve();
    } else {}
    have 1 <= capacity;
    step();
    mark initialize_entry;
    have arena->live_regions == 0;
    loop as initialize_occupied {
        decreases to_integer(capacity) - to_integer(i);
        invariant 0 <= i and i <= capacity;
        invariant forall (k: int32) {
            0 <= k and k < i implies occupied[k] == 0
        };
        owns occupied[0..capacity];

        initialize by solve();
        preserve by {
            mark iteration;
            step();
            step();
            have to_integer(at(iteration, i) + 1) == to_integer(at(iteration, i)) + 1;
            have 0 <= to_integer(capacity) - to_integer(at(iteration, i) + 1);
            solve();
        }
    }
    have at(initialize_entry, arena->live_regions) == 0;
    transport(at(initialize_entry, arena->live_regions) == 0, arena->live_regions == 0) using {
        at(initialize_entry, arena->live_regions) == 0;
    };
    have i == capacity;
    have forall (k: int32) {
        0 <= k and k < capacity implies occupied[k] == 0
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < capacity);
        instantiate(forall (j: int32) {
            0 <= j and j < i implies occupied[j] == 0
        }, k) using {
            0 <= k;
            k < capacity;
            i == capacity;
        };
        assumption();
    }
    step();
    step();
    step();
    have arena->occupied == occupied;
    have arena->capacity == capacity;
    have forall (k: int32) {
        0 <= k and k < arena->capacity implies arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        instantiate(forall (j: int32) {
            0 <= j and j < capacity implies occupied[j] == 0
        }, k) using {
            0 <= k;
            k < capacity;
        };
        have occupied[k] == 0 by { assumption(); }
        rewrite(arena->occupied == occupied);
        assumption();
    }
    fold(arena_initialized_storage(
        arena->data,
        arena->occupied,
        arena->capacity,
        1
    ));
    have arena->capacity <= 1073741823;
    have separate(
        memory(arena->occupied[0..arena->capacity]),
        memory(arena->data[0..arena->capacity])
    ) by {
        both {
            both { solve(); } and { assumption(); }
        } and {
            assumption();
        }
    }
    have separate(
        memory(*arena),
        memory(arena->data[0..arena->capacity])
    ) by {
        both {
            both { solve(); } and { assumption(); }
        } and {
            assumption();
        }
    }
    have separate(
        memory(*arena),
        memory(arena->occupied[0..arena->capacity])
    ) by {
        both {
            both { solve(); } and { assumption(); }
        } and {
            assumption();
        }
    }
    gather(arena_cells(arena->data, arena->occupied, arena->capacity));
    fold(arena_cells(arena->data, arena->occupied, arena->capacity));
    let state = fold(arena_state(arena), { live: 0, capacity: arena->capacity });
    step();
    have forall (k: int32) {
        result == 1 and 0 <= k and k < arena->capacity implies
            arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(result == 1);
        extract(0 <= k);
        extract(k < arena->capacity);
        instantiate(forall (j: int32) {
            0 <= j and j < arena->capacity implies arena->occupied[j] == 0
        }, k) using {
            0 <= k;
            k < arena->capacity;
        };
        assumption();
    }
    let outcome = fold(arena_init_outcome(arena), {
        model: ArenaInitOutcome::Success(0, capacity)
    });
    solve();
}


spec enum ArenaAllocOutcome {
    Failure,
    Success(int32, int32),
}

resource arena_alloc_result(region: struct region*) {
    field model: ArenaAllocOutcome;
    match model {
        ArenaAllocOutcome::Failure => {
            owns *region;
        },
        ArenaAllocOutcome::Success(start, end) => {
            owns allocated: arena_region(region);
            fact allocated.start == start;
            fact allocated.end == end;
        },
    }
}

verifying "arena_alloc.c";

int32 arena_alloc(struct arena* arena, int32 count, struct region* region) {
    owns st: arena_state(arena);
    consumes *region;
    produces outcome: arena_alloc_result(region);
    requires st.live < 2147483647;

    ensures forall (k: int32) {
        result == 0 and 0 <= k and k < arena->capacity implies
            arena->occupied[k] == old(arena->occupied[k])
    };
    ensures result == 0 or result == 1;
    ensures st.live == old(st.live) + result;
    ensures arena->capacity == old(arena->capacity);
    ensures arena->capacity <= 536870911;
    ensures st.capacity == arena->capacity;
    ensures result == 0 implies outcome.model == ArenaAllocOutcome::Failure;
    ensures result == 1 implies outcome.model ==
        ArenaAllocOutcome::Success(region->start, region->end);
    ensures result == 1 implies region->arena == arena;
    ensures result == 1 implies region->end == region->start + count;
    ensures result == 1 implies region->end <= arena->capacity;
    ensures result == 1 implies 0 <= region->start;
    ensures result == 1 implies region->start < region->end;
    ensures forall (k: int32) {
        result == 1 and region->start <= k and k < region->end implies
            arena->occupied[k] == 1
    };
    ensures forall (k: int32) {
        result == 1 and 0 <= k and k < region->start implies
            arena->occupied[k] == old(arena->occupied[k])
    };
    ensures forall (k: int32) {
        result == 1 and region->end <= k and k < arena->capacity implies
            arena->occupied[k] == old(arena->occupied[k])
    };
    ensures forall (k: int32) {
        result == 1 and region->start <= k and k < region->end implies
            old(arena->occupied[k]) == 0
    };
} by {
    let { live: n } = unfold(st);
    step();
    step();
    step();
    step();
    if at(region(4).entry, count) <= at(region(4).entry, 0) {
        step();
        step();
        let st = fold(arena_state(arena), { live: n, capacity: arena->capacity });
        let outcome = fold(arena_alloc_result(region), { model: ArenaAllocOutcome::Failure() });
        have result == 0 by {
            normalize();
        }
        have forall (k: int32) { result == 0 and 0 <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            extract(0 <= k);
            extract(k < arena->capacity);
            transport(old(arena->occupied[k]) == old(arena->occupied[k]), arena->occupied[k] == old(arena->occupied[k])) using {
                0 <= k;
                k < arena->capacity;
            };
        }
        assumption();
        have result == 0 or result == 1 by {
            assumption();
        }
        assumption();
        have to_integer(st.live) == (to_integer(old(st.live)) + to_integer(result)) by {
            normalize();
        }
        assumption();
        have arena->capacity == old(arena->capacity) by {
            normalize();
        }
        assumption();
        have arena->capacity <= 536870911 by {
            assumption();
        }
        assumption();
        have st.capacity == arena->capacity by {
            normalize();
        }
        assumption();
        have result == 0 implies outcome.model == ArenaAllocOutcome::Failure() by {
            intro();
            normalize();
        }
        assumption();
        have result == 1 implies outcome.model == ArenaAllocOutcome::Success(region->start, region->end) by {
            intro();
            contradiction(result == 1);
        }
        assumption();
        have result == 1 implies region->arena == arena by {
            intro();
            contradiction(result == 1);
        }
        assumption();
        have result == 1 implies to_integer(region->end) == (to_integer(region->start) + to_integer(count)) by {
            intro();
            contradiction(result == 1);
        }
        assumption();
        have result == 1 implies region->end <= arena->capacity by {
            intro();
            contradiction(result == 1);
        }
        assumption();
        have result == 1 implies 0 <= region->start by {
            intro();
            contradiction(result == 1);
        }
        assumption();
        have result == 1 implies region->start < region->end by {
            intro();
            contradiction(result == 1);
        }
        assumption();
        have forall (k: int32) { result == 1 and region->start <= k and k < region->end implies arena->occupied[k] == 1 } by {
            intro();
            intro();
            extract(result == 1);
            have not result == 1 by {
                normalize();
            }
            contradiction(result == 1);
        }
        assumption();
        have forall (k: int32) { result == 1 and 0 <= k and k < region->start implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            extract(result == 1);
            have not result == 1 by {
                normalize();
            }
            contradiction(result == 1);
        }
        assumption();
        have forall (k: int32) { result == 1 and region->end <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            extract(result == 1);
            have not result == 1 by {
                normalize();
            }
            contradiction(result == 1);
        }
        assumption();
        have forall (k: int32) { result == 1 and region->start <= k and k < region->end implies old(arena->occupied[k]) == 0 } by {
            intro();
            intro();
            extract(result == 1);
            have not result == 1 by {
                normalize();
            }
            contradiction(result == 1);
        }
        assumption();
        assumption();
        assumption();
    } else {
        step();
        step();
    }
    if at(region(7).entry, count) > at(region(7).entry, arena->capacity) {
        step();
        step();
        let st = fold(arena_state(arena), { live: n, capacity: arena->capacity });
        let outcome = fold(arena_alloc_result(region), { model: ArenaAllocOutcome::Failure() });
        have result == 0 by {
            normalize();
        }
        have forall (k: int32) { result == 0 and 0 <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            extract(0 <= k);
            extract(k < arena->capacity);
            transport(old(arena->occupied[k]) == old(arena->occupied[k]), arena->occupied[k] == old(arena->occupied[k])) using {
                0 <= k;
                k < arena->capacity;
            };
        }
        assumption();
        have result == 0 or result == 1 by {
            assumption();
        }
        assumption();
        have to_integer(st.live) == (to_integer(old(st.live)) + to_integer(result)) by {
            normalize();
        }
        assumption();
        have arena->capacity == old(arena->capacity) by {
            normalize();
        }
        assumption();
        have arena->capacity <= 536870911 by {
            assumption();
        }
        assumption();
        have st.capacity == arena->capacity by {
            normalize();
        }
        assumption();
        have result == 0 implies outcome.model == ArenaAllocOutcome::Failure() by {
            intro();
            normalize();
        }
        assumption();
        have result == 1 implies outcome.model == ArenaAllocOutcome::Success(region->start, region->end) by {
            intro();
            contradiction(result == 1);
        }
        assumption();
        have result == 1 implies region->arena == arena by {
            intro();
            contradiction(result == 1);
        }
        assumption();
        have result == 1 implies to_integer(region->end) == (to_integer(region->start) + to_integer(count)) by {
            intro();
            contradiction(result == 1);
        }
        assumption();
        have result == 1 implies region->end <= arena->capacity by {
            intro();
            contradiction(result == 1);
        }
        assumption();
        have result == 1 implies 0 <= region->start by {
            intro();
            contradiction(result == 1);
        }
        assumption();
        have result == 1 implies region->start < region->end by {
            intro();
            contradiction(result == 1);
        }
        assumption();
        have forall (k: int32) { result == 1 and region->start <= k and k < region->end implies arena->occupied[k] == 1 } by {
            intro();
            intro();
            extract(result == 1);
            have not result == 1 by {
                normalize();
            }
            contradiction(result == 1);
        }
        assumption();
        have forall (k: int32) { result == 1 and 0 <= k and k < region->start implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            extract(result == 1);
            have not result == 1 by {
                normalize();
            }
            contradiction(result == 1);
        }
        assumption();
        have forall (k: int32) { result == 1 and region->end <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            extract(result == 1);
            have not result == 1 by {
                normalize();
            }
            contradiction(result == 1);
        }
        assumption();
        have forall (k: int32) { result == 1 and region->start <= k and k < region->end implies old(arena->occupied[k]) == 0 } by {
            intro();
            intro();
            extract(result == 1);
            have not result == 1 by {
                normalize();
            }
            contradiction(result == 1);
        }
        assumption();
        assumption();
        assumption();
    } else {
        step();
        step();
    }
    have 0 < count by {
        assumption();
    }
    have count <= arena->capacity by {
        assumption();
    }
    unfold(arena_cells(arena->data, arena->occupied, arena->capacity));
    step();
    step();
    have 0 <= arena->capacity by {
        assumption();
    }
    have forall (k: int32) { 0 <= k and k < 0 implies arena->occupied[k] == 0 } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < 0);
        have not k < 0 by {
            assumption();
        }
        contradiction(k < 0);
    }
    have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        transport(old(arena->occupied[k]) == old(arena->occupied[k]), arena->occupied[k] == old(arena->occupied[k])) using {
            0 <= k;
            k < arena->capacity;
        };
    }
    have viewable(arena->occupied[0..arena->capacity]) by {
        transport(at(function.entry, viewable(arena->occupied[0..arena->capacity])), viewable(arena->occupied[0..arena->capacity])) using {
        };
    }
    let run = fold(arena_scan(arena->data, arena->occupied, arena->capacity), { lo: 0, hi: 0 });
    loop as find_first_free_run {
        decreases (to_integer(arena->capacity) - to_integer(i));
        owns run: arena_scan(arena->data, arena->occupied, arena->capacity);
        invariant run.hi == i;
        invariant (to_integer(run.lo) + to_integer(run_length)) == to_integer(i);
        invariant 0 <= run_length and run_length <= count;
        invariant forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == at(find_first_free_run.entry, arena->occupied[k]) };
        invariant arena->data == old(arena->data);
        invariant arena->occupied == old(arena->occupied);
        initialize by {
            have run.hi == i by {
                normalize();
            }
            have (to_integer(run.lo) + to_integer(run_length)) == to_integer(i) by {
                normalize();
            }
            have 0 <= run_length and run_length <= count by {
                both {
                    normalize();
                } and {
                    arithmetic_certificate {
                        premise 0: at(function.entry, 0) < at(function.entry, count) =>
                            at(function.entry, 0) < at(function.entry, count);
                        trivial => -1 <= 0;
                        add 0, 1 => (at(function.entry, 0) + -1) < (at(function.entry,
                            to_integer((count as int32))) + 0);
                        conclusion 2;
                    }
                }
            }
            have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == at(find_first_free_run.entry, arena->occupied[k]) } by {
                assumption();
            }
            have arena->data == old(arena->data) by {
                normalize();
            }
            have arena->occupied == old(arena->occupied) by {
                normalize();
            }
        }
        preserve by {
            mark iteration;
            let { lo: lo, hi: hi } = unfold(run);
            have hi == i by {
                assumption();
            }
            have (to_integer(lo) + to_integer(run_length)) == to_integer(i) by {
                assumption();
            }
            have lo <= i by {
                assumption();
            }
            have 0 <= i by {
                arithmetic_certificate {
                    premise 0: 0 <= lo => 0 <= lo;
                    premise 1: at(function.entry, lo) <= at(function.entry, i) => at(function.entry,
                        lo) <= at(function.entry, i);
                    add 0, 1 => (to_integer((0 as int32)) + at(function.entry, to_integer((lo as
                        int32)))) <= (to_integer((lo as int32)) + at(function.entry, to_integer((i
                        as int32))));
                    conclusion 2;
                }
            }
            have (to_integer(i) + 1) <= to_integer(arena->capacity) by {
                arithmetic_certificate {
                    negated_goal => to_integer(arena->capacity) < (to_integer(i) + 1);
                    premise 0: to_integer(i) < to_integer(arena->capacity) => to_integer(i) <
                        to_integer(arena->capacity);
                    add 0, 1 => (to_integer(arena->capacity) + 1 + (to_integer(i) + 1)) <=
                        (to_integer(i) + 1 + to_integer(arena->capacity));
                    conclusion 2;
                }
            }
            if arena->occupied[i] == 0 {
                have (to_integer(run_length) + 1) <= to_integer(count) by {
                    arithmetic_certificate {
                        negated_goal => to_integer(count) < (to_integer(run_length) + 1);
                        premise 0: to_integer(run_length) < to_integer(count) =>
                            to_integer(run_length) < to_integer(count);
                        add 0, 1 => (to_integer(count) + 1 + (to_integer(run_length) + 1)) <=
                            (to_integer(run_length) + 1 + to_integer(count));
                        conclusion 2;
                    }
                }
                if at(region(13).entry, arena->occupied[i]) == at(region(13).entry, 0) {
                    step();
                    step();
                } else {
                }
                step();
                have forall (k: int32) { lo <= k and k < i implies arena->occupied[k] == 0 } by {
                    intro();
                    intro();
                    extract(lo <= k);
                    extract(k < i);
                    if k < at(iteration, i) {
                        have k < hi by {
                            assumption();
                        }
                        instantiate(forall (j: int32) { lo <= j and j < hi implies arena->occupied[j] == 0 }, k) using {
                            lo <= k;
                            k < hi;
                        };
                    } else {
                        have k <= at(iteration, i) by {
                            arithmetic_certificate signed_int32 {
                                premise 0: (at(region(13).entry, i) as int32) <
                                    (at(region(13).entry, arena->capacity) as int32) =>
                                    (at(region(13).entry, i) as int32) < (at(region(13).entry,
                                    arena->capacity) as int32);
                                premise 1: (k as int32) < (i as int32) => (k as int32) < (i as
                                    int32);
                                premise 2: (0 as int32) <= (at(region(13).entry, i) as int32) => (0
                                    as int32) <= (at(region(13).entry, i) as int32);
                                premise 3: (at(function.entry, arena->capacity) as int32) <=
                                    (at(function.entry, 536870911) as int32) => (at(function.entry,
                                    arena->capacity) as int32) <= (at(function.entry, 536870911) as
                                    int32);
                                add 0, 3 => (to_integer((at(region(13).entry, i) as int32)) +
                                    to_integer((at(function.entry, arena->capacity) as int32))) <
                                    (to_integer((at(region(13).entry, arena->capacity) as int32)) +
                                    to_integer((at(function.entry, 536870911) as int32)));
                                interval_from_affine 2 (at(region(13).entry, i)) (0) (2147483647);
                                interval_from_affine 4 (at(region(13).entry, i)) (-2147483648)
                                    (536870910);
                                interval_intersect 5, 6 (0) (536870910);
                                interval_atom (1) (1) (1);
                                interval_add_bounded 7, 8 (1) (536870911);
                                affine_premise 1 9 9 => to_integer((k as int32)) < to_integer((i as
                                    int32));
                                conclusion 10;
                            }
                        }
                        have k == at(iteration, i) by {
                            arithmetic_certificate {
                                premise 0: k <= at(iteration, i) => k <= at(iteration, i);
                                premise 1: not k < at(region(13).entry, i) => not k <
                                    at(region(13).entry, i);
                                equal_from_bounds 0, 1 => k == at(iteration, i);
                                conclusion 2;
                            }
                        }
                        rewrite(k == at(iteration, i));
                        assumption();
                    }
                }
                have to_integer(at(iteration, i)) < (to_integer(at(iteration, i)) + 1) by {
                    normalize();
                }
                have at(iteration, i) < i by {
                    arithmetic_certificate signed_int32 {
                        premise 0: (at(region(13).entry, i) as int32) < (at(region(13).entry,
                            arena->capacity) as int32) => (at(region(13).entry, i) as int32) <
                            (at(region(13).entry, arena->capacity) as int32);
                        int32_range => to_integer((arena->capacity as int32)) <=
                            to_integer((2147483647 as int32));
                        add 0, 1 => (to_integer((at(region(13).entry, i) as int32)) +
                            to_integer((arena->capacity as int32))) <
                            (to_integer((at(region(13).entry, arena->capacity) as int32)) +
                            to_integer((2147483647 as int32)));
                        interval_from_affine 2 (at(region(13).entry, i)) (-2147483648) (2147483646);
                        interval_atom (1) (1) (1);
                        interval_add_bounded 3, 4 (-2147483647) (2147483647);
                        trivial => 0 <= 0;
                        affine_conclusion 6 5 => (at(iteration, i) as int32) < (i as int32);
                        conclusion 7;
                    }
                }
                have at(iteration, i) <= i by {
                    arithmetic_certificate {
                        premise 0: at(iteration, i) < i => at(iteration, i) < i;
                        trivial => -1 <= 0;
                        add 0, 1 => (at(iteration, to_integer((i as int32))) + -1) < (to_integer((i
                            as int32)) + 0);
                        conclusion 2;
                    }
                }
                have lo <= i by {
                    arithmetic_certificate {
                        premise 0: lo <= at(region(13).entry, i) => lo <= at(region(13).entry, i);
                        premise 1: at(iteration, i) < i => at(iteration, i) < i;
                        add 0, 1 => (to_integer((lo as int32)) + at(iteration, to_integer((i as
                            int32)))) < (at(region(13).entry, to_integer((i as int32))) +
                            to_integer((i as int32)));
                        trivial => -1 <= 0;
                        add 2, 3 => (to_integer((lo as int32)) + at(iteration, to_integer((i as
                            int32))) + -1) < (at(region(13).entry, to_integer((i as int32))) +
                            to_integer((i as int32)) + 0);
                        conclusion 4;
                    }
                }
                have i <= arena->capacity by {
                    arithmetic_certificate signed_int32 {
                        premise 0: (at(region(13).entry, i) as int32) < (at(region(13).entry,
                            arena->capacity) as int32) => (at(region(13).entry, i) as int32) <
                            (at(region(13).entry, arena->capacity) as int32);
                        int32_range => to_integer((arena->capacity as int32)) <=
                            to_integer((2147483647 as int32));
                        add 0, 1 => (to_integer((at(region(13).entry, i) as int32)) +
                            to_integer((arena->capacity as int32))) <
                            (to_integer((at(region(13).entry, arena->capacity) as int32)) +
                            to_integer((2147483647 as int32)));
                        interval_from_affine 2 (at(region(13).entry, i)) (-2147483648) (2147483646);
                        interval_atom (1) (1) (1);
                        interval_add_bounded 3, 4 (-2147483647) (2147483647);
                        affine_conclusion 0 5 => (i as int32) <= (arena->capacity as int32);
                        conclusion 6;
                    }
                }
                have to_integer(run_length) == (to_integer(at(iteration, run_length)) + 1) by {
                    have -2147483648 <= (to_integer(at(iteration, run_length)) + 1) by {
                        arithmetic_certificate {
                            negated_goal => (to_integer(at(iteration, run_length)) + 1) <
                                -2147483648;
                            premise 0: 0 <= to_integer(at(iteration, run_length)) => 0 <=
                                to_integer(at(iteration, run_length));
                            add 0, 1 => (to_integer(at(iteration, run_length)) + 1 + 0) <
                                (-2147483648 + to_integer(at(iteration, run_length)));
                            conclusion 2;
                        }
                    }
                    have (to_integer(at(iteration, run_length)) + 1) <= 2147483647 by {
                        arithmetic_certificate {
                            negated_goal => 2147483647 < (to_integer(at(iteration, run_length)) +
                                1);
                            premise 0: (let integer_value: Integer = to_integer(at(region(13).entry,
                                (i as int32))) + 1; integer_value) <= to_integer(at(region(0).entry,
                                (arena->capacity as int32))) => (let integer_value: Integer =
                                to_integer(at(region(13).entry, (i as int32))) + 1; integer_value)
                                <= to_integer(at(region(0).entry, (arena->capacity as int32)));
                            premise 1: (let integer_value: Integer = to_integer((lo as int32)) +
                                to_integer(at(region(13).entry, (run_length as int32)));
                                integer_value) == to_integer(at(region(13).entry, (i as int32))) =>
                                (let integer_value: Integer = to_integer((lo as int32)) +
                                to_integer(at(region(13).entry, (run_length as int32)));
                                integer_value) == to_integer(at(region(13).entry, (i as int32)));
                            less_equal_from_equal 2 => (let integer_value: Integer = to_integer((lo
                                as int32)) + to_integer(at(region(13).entry, (run_length as
                                int32))); integer_value) <= to_integer(at(region(13).entry, (i as
                                int32)));
                            premise 2: 0 <= to_integer((lo as int32)) => 0 <= to_integer((lo as
                                int32));
                            premise 3: to_integer(at(region(0).entry, (arena->capacity as int32)))
                                <= 536870911 => to_integer(at(region(0).entry, (arena->capacity as
                                int32))) <= 536870911;
                            add 0, 1 => (2147483647 + (let integer_value: Integer =
                                to_integer(at(region(13).entry, (i as int32))) + 1; integer_value))
                                < (to_integer(at(iteration, run_length)) + 1 +
                                to_integer(at(region(0).entry, (arena->capacity as int32))));
                            add 6, 3 => (2147483647 + (let integer_value: Integer =
                                to_integer(at(region(13).entry, (i as int32))) + 1; integer_value) +
                                (let integer_value: Integer = to_integer((lo as int32)) +
                                to_integer(at(region(13).entry, (run_length as int32)));
                                integer_value)) < (to_integer(at(iteration, run_length)) + 1 +
                                to_integer(at(region(0).entry, (arena->capacity as int32))) +
                                to_integer(at(region(13).entry, (i as int32))));
                            add 7, 4 => (2147483647 + (let integer_value: Integer =
                                to_integer(at(region(13).entry, (i as int32))) + 1; integer_value) +
                                (let integer_value: Integer = to_integer((lo as int32)) +
                                to_integer(at(region(13).entry, (run_length as int32)));
                                integer_value) + 0) < (to_integer(at(iteration, run_length)) + 1 +
                                to_integer(at(region(0).entry, (arena->capacity as int32))) +
                                to_integer(at(region(13).entry, (i as int32))) + to_integer((lo as
                                int32)));
                            add 8, 5 => (2147483647 + (let integer_value: Integer =
                                to_integer(at(region(13).entry, (i as int32))) + 1; integer_value) +
                                (let integer_value: Integer = to_integer((lo as int32)) +
                                to_integer(at(region(13).entry, (run_length as int32)));
                                integer_value) + 0 + to_integer(at(region(0).entry, (arena->capacity
                                as int32)))) < (to_integer(at(iteration, run_length)) + 1 +
                                to_integer(at(region(0).entry, (arena->capacity as int32))) +
                                to_integer(at(region(13).entry, (i as int32))) + to_integer((lo as
                                int32)) + 536870911);
                            conclusion 9;
                        }
                    }
                    have to_integer(run_length) == (to_integer(at(iteration, run_length)) + 1) by {
                        arithmetic_certificate rules {
                            premise 0: -2147483648 <= (to_integer(at(iteration, run_length)) + 1) =>
                                -2147483648 <= (to_integer(at(iteration, run_length)) + 1);
                            premise 1: (to_integer(at(iteration, run_length)) + 1) <= 2147483647 =>
                                (to_integer(at(iteration, run_length)) + 1) <= 2147483647;
                            integer_operation_identity bounds [0, 1] => to_integer(run_length) ==
                                (to_integer(at(iteration, run_length)) + 1);
                            conclusion 0;
                        }
                    }
                    assumption();
                }
                have (to_integer(lo) + to_integer(at(iteration, run_length))) == to_integer(at(iteration, i)) by {
                    assumption();
                }
                have (to_integer(lo) + to_integer(run_length)) == to_integer(i) by {
                    have (to_integer(lo) + to_integer(run_length)) <= to_integer(i) by {
                        arithmetic_certificate {
                            negated_goal => to_integer(i) < (to_integer(lo) +
                                to_integer(run_length));
                            premise 0: (to_integer(lo) + to_integer(at(iteration, run_length))) ==
                                to_integer(at(iteration, i)) => (to_integer(lo) +
                                to_integer(at(iteration, run_length))) == to_integer(at(iteration,
                                i));
                            less_equal_from_equal 1 => (to_integer(lo) + to_integer(at(iteration,
                                run_length))) <= to_integer(at(iteration, i));
                            premise 1: to_integer(run_length) == (to_integer(at(iteration,
                                run_length)) + 1) => to_integer(run_length) ==
                                (to_integer(at(iteration, run_length)) + 1);
                            less_equal_from_equal 3 => to_integer(run_length) <=
                                (to_integer(at(iteration, run_length)) + 1);
                            premise 2: to_integer(at(iteration, i)) < to_integer(i) =>
                                to_integer(at(iteration, i)) < to_integer(i);
                            add 0, 2 => (to_integer(i) + (to_integer(lo) + to_integer(at(iteration,
                                run_length)))) < (to_integer(lo) + to_integer(run_length) +
                                to_integer(at(iteration, i)));
                            add 6, 4 => (to_integer(i) + (to_integer(lo) + to_integer(at(iteration,
                                run_length))) + to_integer(run_length)) < (to_integer(lo) +
                                to_integer(run_length) + to_integer(at(iteration, i)) +
                                (to_integer(at(iteration, run_length)) + 1));
                            add 7, 5 => (to_integer(i) + (to_integer(lo) + to_integer(at(iteration,
                                run_length))) + to_integer(run_length) + 1 +
                                (to_integer(at(iteration, i)) + 1)) <= (to_integer(lo) +
                                to_integer(run_length) + to_integer(at(iteration, i)) +
                                (to_integer(at(iteration, run_length)) + 1) + to_integer(i));
                            conclusion 8;
                        }
                    }
                    have to_integer(i) <= (to_integer(lo) + to_integer(run_length)) by {
                        have -2147483648 <= (to_integer(at(iteration, run_length)) + 1) by {
                            arithmetic_certificate {
                                negated_goal => (to_integer(at(iteration, run_length)) + 1) <
                                    -2147483648;
                                premise 0: 0 <= to_integer(at(iteration, run_length)) => 0 <=
                                    to_integer(at(iteration, run_length));
                                add 0, 1 => (to_integer(at(iteration, run_length)) + 1 + 0) <
                                    (-2147483648 + to_integer(at(iteration, run_length)));
                                conclusion 2;
                            }
                        }
                        have (to_integer(at(iteration, run_length)) + 1) <= 2147483647 by {
                            arithmetic_certificate {
                                negated_goal => 2147483647 < (to_integer(at(iteration, run_length))
                                    + 1);
                                premise 0: (let integer_value: Integer =
                                    to_integer(at(region(13).entry, (i as int32))) + 1;
                                    integer_value) <= to_integer(at(region(0).entry,
                                    (arena->capacity as int32))) => (let integer_value: Integer =
                                    to_integer(at(region(13).entry, (i as int32))) + 1;
                                    integer_value) <= to_integer(at(region(0).entry,
                                    (arena->capacity as int32)));
                                premise 1: (to_integer(lo) + to_integer(at(iteration, run_length)))
                                    == to_integer(at(iteration, i)) => (to_integer(lo) +
                                    to_integer(at(iteration, run_length))) ==
                                    to_integer(at(iteration, i));
                                less_equal_from_equal 2 => (to_integer(lo) +
                                    to_integer(at(iteration, run_length))) <=
                                    to_integer(at(iteration, i));
                                premise 2: 0 <= to_integer(lo) => 0 <= to_integer(lo);
                                premise 3: to_integer(at(region(0).entry, (arena->capacity as
                                    int32))) <= 536870911 => to_integer(at(region(0).entry,
                                    (arena->capacity as int32))) <= 536870911;
                                add 0, 1 => (2147483647 + (let integer_value: Integer =
                                    to_integer(at(region(13).entry, (i as int32))) + 1;
                                    integer_value)) < (to_integer(at(iteration, run_length)) + 1 +
                                    to_integer(at(region(0).entry, (arena->capacity as int32))));
                                add 6, 3 => (2147483647 + (let integer_value: Integer =
                                    to_integer(at(region(13).entry, (i as int32))) + 1;
                                    integer_value) + (to_integer(lo) + to_integer(at(iteration,
                                    run_length)))) < (to_integer(at(iteration, run_length)) + 1 +
                                    to_integer(at(region(0).entry, (arena->capacity as int32))) +
                                    to_integer(at(iteration, i)));
                                add 7, 4 => (2147483647 + (let integer_value: Integer =
                                    to_integer(at(region(13).entry, (i as int32))) + 1;
                                    integer_value) + (to_integer(lo) + to_integer(at(iteration,
                                    run_length))) + 0) < (to_integer(at(iteration, run_length)) + 1
                                    + to_integer(at(region(0).entry, (arena->capacity as int32))) +
                                    to_integer(at(iteration, i)) + to_integer(lo));
                                add 8, 5 => (2147483647 + (let integer_value: Integer =
                                    to_integer(at(region(13).entry, (i as int32))) + 1;
                                    integer_value) + (to_integer(lo) + to_integer(at(iteration,
                                    run_length))) + 0 + to_integer(at(region(0).entry,
                                    (arena->capacity as int32)))) < (to_integer(at(iteration,
                                    run_length)) + 1 + to_integer(at(region(0).entry,
                                    (arena->capacity as int32))) + to_integer(at(iteration, i)) +
                                    to_integer(lo) + 536870911);
                                conclusion 9;
                            }
                        }
                        have to_integer(run_length) == (to_integer(at(iteration, run_length)) + 1) by {
                            arithmetic_certificate rules {
                                premise 0: -2147483648 <= (to_integer(at(iteration, run_length)) +
                                    1) => -2147483648 <= (to_integer(at(iteration, run_length)) +
                                    1);
                                premise 1: (to_integer(at(iteration, run_length)) + 1) <= 2147483647
                                    => (to_integer(at(iteration, run_length)) + 1) <= 2147483647;
                                integer_operation_identity bounds [0, 1] => to_integer(run_length)
                                    == (to_integer(at(iteration, run_length)) + 1);
                                conclusion 0;
                            }
                        }
                        have -2147483648 <= (to_integer(at(iteration, i)) + 1) by {
                            arithmetic_certificate {
                                negated_goal => (to_integer(at(iteration, i)) + 1) < -2147483648;
                                premise 0: 0 <= to_integer(at(iteration, i)) => 0 <=
                                    to_integer(at(iteration, i));
                                add 0, 1 => (to_integer(at(iteration, i)) + 1 + 0) < (-2147483648 +
                                    to_integer(at(iteration, i)));
                                conclusion 2;
                            }
                        }
                        have (to_integer(at(iteration, i)) + 1) <= 2147483647 by {
                            arithmetic_certificate {
                                negated_goal => 2147483647 < (to_integer(at(iteration, i)) + 1);
                                premise 0: (let integer_value: Integer =
                                    to_integer(at(region(13).entry, (i as int32))) + 1;
                                    integer_value) <= to_integer(at(region(0).entry,
                                    (arena->capacity as int32))) => (let integer_value: Integer =
                                    to_integer(at(region(13).entry, (i as int32))) + 1;
                                    integer_value) <= to_integer(at(region(0).entry,
                                    (arena->capacity as int32)));
                                premise 1: to_integer(at(region(0).entry, (arena->capacity as
                                    int32))) <= 536870911 => to_integer(at(region(0).entry,
                                    (arena->capacity as int32))) <= 536870911;
                                add 0, 1 => (2147483647 + (let integer_value: Integer =
                                    to_integer(at(region(13).entry, (i as int32))) + 1;
                                    integer_value)) < (to_integer(at(iteration, i)) + 1 +
                                    to_integer(at(region(0).entry, (arena->capacity as int32))));
                                add 3, 2 => (2147483647 + (let integer_value: Integer =
                                    to_integer(at(region(13).entry, (i as int32))) + 1;
                                    integer_value) + to_integer(at(region(0).entry, (arena->capacity
                                    as int32)))) < (to_integer(at(iteration, i)) + 1 +
                                    to_integer(at(region(0).entry, (arena->capacity as int32))) +
                                    536870911);
                                conclusion 4;
                            }
                        }
                        have to_integer(i) == (to_integer(at(iteration, i)) + 1) by {
                            arithmetic_certificate rules {
                                premise 0: -2147483648 <= (to_integer(at(iteration, i)) + 1) =>
                                    -2147483648 <= (to_integer(at(iteration, i)) + 1);
                                premise 1: (to_integer(at(iteration, i)) + 1) <= 2147483647 =>
                                    (to_integer(at(iteration, i)) + 1) <= 2147483647;
                                integer_operation_identity bounds [0, 1] => to_integer(i) ==
                                    (to_integer(at(iteration, i)) + 1);
                                conclusion 0;
                            }
                        }
                        arithmetic_certificate {
                            negated_goal => (to_integer(lo) + to_integer(run_length)) <
                                to_integer(i);
                            premise 0: (to_integer(lo) + to_integer(at(iteration, run_length))) ==
                                to_integer(at(iteration, i)) => (to_integer(lo) +
                                to_integer(at(iteration, run_length))) == to_integer(at(iteration,
                                i));
                            less_equal_from_equal 1 reverse => to_integer(at(iteration, i)) <=
                                (to_integer(lo) + to_integer(at(iteration, run_length)));
                            premise 1: to_integer(i) == (to_integer(at(iteration, i)) + 1) =>
                                to_integer(i) == (to_integer(at(iteration, i)) + 1);
                            less_equal_from_equal 3 => to_integer(i) <= (to_integer(at(iteration,
                                i)) + 1);
                            premise 2: to_integer(run_length) == (to_integer(at(iteration,
                                run_length)) + 1) => to_integer(run_length) ==
                                (to_integer(at(iteration, run_length)) + 1);
                            less_equal_from_equal 5 reverse => (to_integer(at(iteration,
                                run_length)) + 1) <= to_integer(run_length);
                            add 0, 2 => (to_integer(lo) + to_integer(run_length) +
                                to_integer(at(iteration, i))) < (to_integer(i) + (to_integer(lo) +
                                to_integer(at(iteration, run_length))));
                            add 7, 4 => (to_integer(lo) + to_integer(run_length) +
                                to_integer(at(iteration, i)) + to_integer(i)) < (to_integer(i) +
                                (to_integer(lo) + to_integer(at(iteration, run_length))) +
                                (to_integer(at(iteration, i)) + 1));
                            add 8, 6 => (to_integer(lo) + to_integer(run_length) +
                                to_integer(at(iteration, i)) + to_integer(i) +
                                (to_integer(at(iteration, run_length)) + 1)) < (to_integer(i) +
                                (to_integer(lo) + to_integer(at(iteration, run_length))) +
                                (to_integer(at(iteration, i)) + 1) + to_integer(run_length));
                            conclusion 9;
                        }
                    }
                    arithmetic_certificate {
                        premise 0: (to_integer(lo) + to_integer(run_length)) <= to_integer(i) =>
                            (to_integer(lo) + to_integer(run_length)) <= to_integer(i);
                        premise 1: to_integer(i) <= (to_integer(lo) + to_integer(run_length)) =>
                            to_integer(i) <= (to_integer(lo) + to_integer(run_length));
                        equal_from_bounds 0, 1 => (to_integer(lo) + to_integer(run_length)) ==
                            to_integer(i);
                        conclusion 2;
                    }
                }
                have 0 <= run_length and run_length <= count by {
                    both {
                        arithmetic_certificate signed_int32 {
                            premise 0: (at(region(13).entry, 0) as int32) <= (at(region(13).entry,
                                run_length) as int32) => (at(region(13).entry, 0) as int32) <=
                                (at(region(13).entry, run_length) as int32);
                            premise 1: (at(region(13).entry, run_length) as int32) <
                                (at(region(13).entry, count) as int32) => (at(region(13).entry,
                                run_length) as int32) < (at(region(13).entry, count) as int32);
                            int32_range => to_integer((count as int32)) <= to_integer((2147483647 as
                                int32));
                            add 1, 2 => (to_integer((at(region(13).entry, run_length) as int32)) +
                                to_integer((count as int32))) < (to_integer((at(region(13).entry,
                                count) as int32)) + to_integer((2147483647 as int32)));
                            interval_from_affine 0 (at(region(13).entry, run_length)) (0)
                                (2147483647);
                            interval_from_affine 3 (at(region(13).entry, run_length)) (-2147483648)
                                (2147483646);
                            interval_intersect 4, 5 (0) (2147483646);
                            interval_atom (1) (1) (1);
                            interval_add_bounded 6, 7 (1) (2147483647);
                            trivial => -1 <= 0;
                            add 0, 9 => (to_integer((at(region(13).entry, 0) as int32)) + -1) <=
                                (to_integer((at(region(13).entry, run_length) as int32)) + 0);
                            affine_conclusion 10 8 => (0 as int32) <= (run_length as int32);
                            conclusion 11;
                        }
                    } and {
                        assumption();
                    }
                }
                have viewable(arena->occupied[0..arena->capacity]) by {
                    transport(at(find_first_free_run.entry, viewable(arena->occupied[0..arena->capacity])), viewable(arena->occupied[0..arena->capacity])) using {
                        at(find_first_free_run.entry,
                            viewable(arena->occupied[0..arena->capacity]));
                    };
                }
                let run = fold(arena_scan(arena->data, arena->occupied, arena->capacity), { lo: lo, hi: i });
                have run.hi == i by {
                    normalize();
                }
                have (to_integer(run.lo) + to_integer(run_length)) == to_integer(i) by {
                    assumption();
                }
                have 0 <= at(iteration, i) by {
                    assumption();
                }
                have to_integer((at(iteration, i) + 1)) == (to_integer(at(iteration, i)) + 1) by {
                    have -2147483648 <= (to_integer(at(iteration, i)) + 1) by {
                        arithmetic_certificate {
                            negated_goal => (to_integer(at(iteration, i)) + 1) < -2147483648;
                            premise 0: 0 <= to_integer(at(iteration, i)) => 0 <=
                                to_integer(at(iteration, i));
                            add 0, 1 => (to_integer(at(iteration, i)) + 1 + 0) < (-2147483648 +
                                to_integer(at(iteration, i)));
                            conclusion 2;
                        }
                    }
                    have (to_integer(at(iteration, i)) + 1) <= 2147483647 by {
                        arithmetic_certificate {
                            negated_goal => 2147483647 < (to_integer(at(iteration, i)) + 1);
                            premise 0: (let integer_value: Integer = to_integer(at(region(13).entry,
                                (i as int32))) + 1; integer_value) <= to_integer(at(region(0).entry,
                                (arena->capacity as int32))) => (let integer_value: Integer =
                                to_integer(at(region(13).entry, (i as int32))) + 1; integer_value)
                                <= to_integer(at(region(0).entry, (arena->capacity as int32)));
                            premise 1: to_integer(at(region(0).entry, (arena->capacity as int32)))
                                <= 536870911 => to_integer(at(region(0).entry, (arena->capacity as
                                int32))) <= 536870911;
                            add 0, 1 => (2147483647 + (let integer_value: Integer =
                                to_integer(at(region(13).entry, (i as int32))) + 1; integer_value))
                                < (to_integer(at(iteration, i)) + 1 + to_integer(at(region(0).entry,
                                (arena->capacity as int32))));
                            add 3, 2 => (2147483647 + (let integer_value: Integer =
                                to_integer(at(region(13).entry, (i as int32))) + 1; integer_value) +
                                to_integer(at(region(0).entry, (arena->capacity as int32)))) <
                                (to_integer(at(iteration, i)) + 1 + to_integer(at(region(0).entry,
                                (arena->capacity as int32))) + 536870911);
                            conclusion 4;
                        }
                    }
                    have to_integer((at(iteration, i) + 1)) == (to_integer(at(iteration, i)) + 1) by {
                        arithmetic_certificate rules {
                            premise 0: -2147483648 <= (to_integer(at(iteration, i)) + 1) =>
                                -2147483648 <= (to_integer(at(iteration, i)) + 1);
                            premise 1: (to_integer(at(iteration, i)) + 1) <= 2147483647 =>
                                (to_integer(at(iteration, i)) + 1) <= 2147483647;
                            integer_operation_identity bounds [0, 1] => to_integer((at(iteration, i)
                                + 1)) == (to_integer(at(iteration, i)) + 1);
                            conclusion 0;
                        }
                    }
                    assumption();
                }
                have 0 <= (to_integer(arena->capacity) - to_integer((at(iteration, i) + 1))) by {
                    arithmetic_certificate {
                        negated_goal => (to_integer(arena->capacity) - to_integer((at(iteration, i)
                            + 1))) < 0;
                        premise 0: (let integer_value: Integer = to_integer(at(region(13).entry, (i
                            as int32))) + 1; integer_value) <= to_integer(at(region(0).entry,
                            (arena->capacity as int32))) => (let integer_value: Integer =
                            to_integer(at(region(13).entry, (i as int32))) + 1; integer_value) <=
                            to_integer(at(region(0).entry, (arena->capacity as int32)));
                        premise 1: to_integer((at(iteration, i) + 1)) == (to_integer(at(iteration,
                            i)) + 1) => to_integer((at(iteration, i) + 1)) ==
                            (to_integer(at(iteration, i)) + 1);
                        less_equal_from_equal 2 => to_integer((at(iteration, i) + 1)) <=
                            (to_integer(at(iteration, i)) + 1);
                        add 0, 1 => ((to_integer(arena->capacity) - to_integer((at(iteration, i) +
                            1))) + (let integer_value: Integer = to_integer(at(region(13).entry, (i
                            as int32))) + 1; integer_value)) < (0 + to_integer(at(region(0).entry,
                            (arena->capacity as int32))));
                        add 4, 3 => ((to_integer(arena->capacity) - to_integer((at(iteration, i) +
                            1))) + (let integer_value: Integer = to_integer(at(region(13).entry, (i
                            as int32))) + 1; integer_value) + to_integer((at(iteration, i) + 1))) <
                            (0 + to_integer(at(region(0).entry, (arena->capacity as int32))) +
                            (to_integer(at(iteration, i)) + 1));
                        conclusion 5;
                    }
                }
                have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == at(find_first_free_run.entry, arena->occupied[k]) } by {
                    intro();
                    intro();
                    extract(0 <= k);
                    extract(k < arena->capacity);
                    have at(iteration, arena->occupied[k]) == at(find_first_free_run.entry, arena->occupied[k]) by {
                        instantiate(forall (j: int32) { at(iteration, 0) <= at(iteration, j) and at(iteration, j) < at(iteration, arena->capacity) implies at(iteration, arena->occupied[j]) == at(find_first_free_run.entry, arena->occupied[j]) }, k) using {
                            0 <= k;
                            k < arena->capacity;
                        };
                    }
                    transport(at(iteration, arena->occupied[k]) == at(find_first_free_run.entry, arena->occupied[k]), arena->occupied[k] == at(find_first_free_run.entry, arena->occupied[k])) using {
                        at(iteration, arena->occupied[k]) == at(find_first_free_run.entry,
                            arena->occupied[k]);
                        0 <= k;
                        k < arena->capacity;
                    };
                }
                have arena->data == old(arena->data) by {
                    normalize();
                }
                have arena->occupied == old(arena->occupied) by {
                    normalize();
                }
                have (to_integer(arena->capacity) - to_integer(i)) < at(region(13).entry, (to_integer(arena->capacity) - to_integer(i))) by {
                    rewrite(to_integer((at(iteration, i) + 1)) == (to_integer(at(iteration, i)) + 1));
                    normalize();
                }
            } else {
                if at(region(13).entry, arena->occupied[i]) == at(region(13).entry, 0) {
                } else {
                    step();
                    step();
                }
                step();
                have forall (k: int32) { i <= k and k < i implies arena->occupied[k] == 0 } by {
                    intro();
                    intro();
                    extract(i <= k);
                    extract(k < i);
                    have not k < i by {
                        assumption();
                    }
                    contradiction(k < i);
                }
                have 0 <= i by {
                    arithmetic_certificate signed_int32 {
                        premise 0: (0 as int32) <= (at(region(13).entry, i) as int32) => (0 as
                            int32) <= (at(region(13).entry, i) as int32);
                        premise 1: (at(region(13).entry, i) as int32) < (at(region(13).entry,
                            arena->capacity) as int32) => (at(region(13).entry, i) as int32) <
                            (at(region(13).entry, arena->capacity) as int32);
                        int32_range => to_integer((arena->capacity as int32)) <=
                            to_integer((2147483647 as int32));
                        add 1, 2 => (to_integer((at(region(13).entry, i) as int32)) +
                            to_integer((arena->capacity as int32))) <
                            (to_integer((at(region(13).entry, arena->capacity) as int32)) +
                            to_integer((2147483647 as int32)));
                        interval_from_affine 0 (at(region(13).entry, i)) (0) (2147483647);
                        interval_from_affine 3 (at(region(13).entry, i)) (-2147483648) (2147483646);
                        interval_intersect 4, 5 (0) (2147483646);
                        interval_atom (1) (1) (1);
                        interval_add_bounded 6, 7 (1) (2147483647);
                        trivial => -1 <= 0;
                        add 0, 9 => (to_integer((0 as int32)) + -1) <=
                            (to_integer((at(region(13).entry, i) as int32)) + 0);
                        affine_conclusion 10 8 => (0 as int32) <= (i as int32);
                        conclusion 11;
                    }
                }
                have i <= arena->capacity by {
                    arithmetic_certificate signed_int32 {
                        premise 0: (at(region(13).entry, i) as int32) < (at(region(13).entry,
                            arena->capacity) as int32) => (at(region(13).entry, i) as int32) <
                            (at(region(13).entry, arena->capacity) as int32);
                        int32_range => to_integer((arena->capacity as int32)) <=
                            to_integer((2147483647 as int32));
                        add 0, 1 => (to_integer((at(region(13).entry, i) as int32)) +
                            to_integer((arena->capacity as int32))) <
                            (to_integer((at(region(13).entry, arena->capacity) as int32)) +
                            to_integer((2147483647 as int32)));
                        interval_from_affine 2 (at(region(13).entry, i)) (-2147483648) (2147483646);
                        interval_atom (1) (1) (1);
                        interval_add_bounded 3, 4 (-2147483647) (2147483647);
                        affine_conclusion 0 5 => (i as int32) <= (arena->capacity as int32);
                        conclusion 6;
                    }
                }
                have viewable(arena->occupied[0..arena->capacity]) by {
                    transport(at(find_first_free_run.entry, viewable(arena->occupied[0..arena->capacity])), viewable(arena->occupied[0..arena->capacity])) using {
                        at(find_first_free_run.entry,
                            viewable(arena->occupied[0..arena->capacity]));
                    };
                }
                let run = fold(arena_scan(arena->data, arena->occupied, arena->capacity), { lo: i, hi: i });
                have 0 <= at(iteration, i) by {
                    assumption();
                }
                have to_integer((at(iteration, i) + 1)) == (to_integer(at(iteration, i)) + 1) by {
                    have -2147483648 <= (to_integer(at(iteration, i)) + 1) by {
                        arithmetic_certificate {
                            negated_goal => (to_integer(at(iteration, i)) + 1) < -2147483648;
                            premise 0: 0 <= to_integer(at(iteration, i)) => 0 <=
                                to_integer(at(iteration, i));
                            add 0, 1 => (to_integer(at(iteration, i)) + 1 + 0) < (-2147483648 +
                                to_integer(at(iteration, i)));
                            conclusion 2;
                        }
                    }
                    have (to_integer(at(iteration, i)) + 1) <= 2147483647 by {
                        arithmetic_certificate {
                            negated_goal => 2147483647 < (to_integer(at(iteration, i)) + 1);
                            premise 0: (let integer_value: Integer = to_integer(at(region(13).entry,
                                (i as int32))) + 1; integer_value) <= to_integer(at(region(0).entry,
                                (arena->capacity as int32))) => (let integer_value: Integer =
                                to_integer(at(region(13).entry, (i as int32))) + 1; integer_value)
                                <= to_integer(at(region(0).entry, (arena->capacity as int32)));
                            premise 1: to_integer(at(region(0).entry, (arena->capacity as int32)))
                                <= 536870911 => to_integer(at(region(0).entry, (arena->capacity as
                                int32))) <= 536870911;
                            add 0, 1 => (2147483647 + (let integer_value: Integer =
                                to_integer(at(region(13).entry, (i as int32))) + 1; integer_value))
                                < (to_integer(at(iteration, i)) + 1 + to_integer(at(region(0).entry,
                                (arena->capacity as int32))));
                            add 3, 2 => (2147483647 + (let integer_value: Integer =
                                to_integer(at(region(13).entry, (i as int32))) + 1; integer_value) +
                                to_integer(at(region(0).entry, (arena->capacity as int32)))) <
                                (to_integer(at(iteration, i)) + 1 + to_integer(at(region(0).entry,
                                (arena->capacity as int32))) + 536870911);
                            conclusion 4;
                        }
                    }
                    have to_integer((at(iteration, i) + 1)) == (to_integer(at(iteration, i)) + 1) by {
                        arithmetic_certificate rules {
                            premise 0: -2147483648 <= (to_integer(at(iteration, i)) + 1) =>
                                -2147483648 <= (to_integer(at(iteration, i)) + 1);
                            premise 1: (to_integer(at(iteration, i)) + 1) <= 2147483647 =>
                                (to_integer(at(iteration, i)) + 1) <= 2147483647;
                            integer_operation_identity bounds [0, 1] => to_integer((at(iteration, i)
                                + 1)) == (to_integer(at(iteration, i)) + 1);
                            conclusion 0;
                        }
                    }
                    assumption();
                }
                have 0 <= (to_integer(arena->capacity) - to_integer((at(iteration, i) + 1))) by {
                    arithmetic_certificate {
                        negated_goal => (to_integer(arena->capacity) - to_integer((at(iteration, i)
                            + 1))) < 0;
                        premise 0: (let integer_value: Integer = to_integer(at(region(13).entry, (i
                            as int32))) + 1; integer_value) <= to_integer(at(region(0).entry,
                            (arena->capacity as int32))) => (let integer_value: Integer =
                            to_integer(at(region(13).entry, (i as int32))) + 1; integer_value) <=
                            to_integer(at(region(0).entry, (arena->capacity as int32)));
                        premise 1: to_integer((at(iteration, i) + 1)) == (to_integer(at(iteration,
                            i)) + 1) => to_integer((at(iteration, i) + 1)) ==
                            (to_integer(at(iteration, i)) + 1);
                        less_equal_from_equal 2 => to_integer((at(iteration, i) + 1)) <=
                            (to_integer(at(iteration, i)) + 1);
                        add 0, 1 => ((to_integer(arena->capacity) - to_integer((at(iteration, i) +
                            1))) + (let integer_value: Integer = to_integer(at(region(13).entry, (i
                            as int32))) + 1; integer_value)) < (0 + to_integer(at(region(0).entry,
                            (arena->capacity as int32))));
                        add 4, 3 => ((to_integer(arena->capacity) - to_integer((at(iteration, i) +
                            1))) + (let integer_value: Integer = to_integer(at(region(13).entry, (i
                            as int32))) + 1; integer_value) + to_integer((at(iteration, i) + 1))) <
                            (0 + to_integer(at(region(0).entry, (arena->capacity as int32))) +
                            (to_integer(at(iteration, i)) + 1));
                        conclusion 5;
                    }
                }
                have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == at(find_first_free_run.entry, arena->occupied[k]) } by {
                    intro();
                    intro();
                    extract(0 <= k);
                    extract(k < arena->capacity);
                    have at(iteration, arena->occupied[k]) == at(find_first_free_run.entry, arena->occupied[k]) by {
                        instantiate(forall (j: int32) { at(iteration, 0) <= at(iteration, j) and at(iteration, j) < at(iteration, arena->capacity) implies at(iteration, arena->occupied[j]) == at(find_first_free_run.entry, arena->occupied[j]) }, k) using {
                            0 <= k;
                            k < arena->capacity;
                        };
                    }
                    transport(at(iteration, arena->occupied[k]) == at(find_first_free_run.entry, arena->occupied[k]), arena->occupied[k] == at(find_first_free_run.entry, arena->occupied[k])) using {
                        at(iteration, arena->occupied[k]) == at(find_first_free_run.entry,
                            arena->occupied[k]);
                        0 <= k;
                        k < arena->capacity;
                    };
                }
                have run.hi == i by {
                    normalize();
                }
                have run.hi == i implies (to_integer(run.lo) + to_integer(run_length)) == to_integer(i) by {
                    intro();
                    normalize();
                }
                have run.hi == i implies (to_integer(run.lo) + to_integer(run_length)) == to_integer(i) implies 0 <= run_length and run_length <= count by {
                    intro();
                    intro();
                    both {
                        normalize();
                    } and {
                        arithmetic_certificate {
                            premise 0: at(function.entry, 0) < at(function.entry, count) =>
                                at(function.entry, 0) < at(function.entry, count);
                            trivial => -1 <= 0;
                            add 0, 1 => (at(function.entry, 0) + -1) < (at(function.entry,
                                to_integer((count as int32))) + 0);
                            conclusion 2;
                        }
                    }
                }
                have run.hi == i implies (to_integer(run.lo) + to_integer(run_length)) == to_integer(i) implies 0 <= run_length and run_length <= count implies forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == at(find_first_free_run.entry, arena->occupied[k]) } by {
                    intro();
                    intro();
                    intro();
                    assumption();
                }
                have run.hi == i implies (to_integer(run.lo) + to_integer(run_length)) == to_integer(i) implies 0 <= run_length and run_length <= count implies forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == at(find_first_free_run.entry, arena->occupied[k]) } implies arena->data == old(arena->data) by {
                    intro();
                    intro();
                    intro();
                    intro();
                    normalize();
                }
                have run.hi == i implies (to_integer(run.lo) + to_integer(run_length)) == to_integer(i) implies 0 <= run_length and run_length <= count implies forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == at(find_first_free_run.entry, arena->occupied[k]) } implies arena->data == old(arena->data) implies arena->occupied == old(arena->occupied) by {
                    intro();
                    intro();
                    intro();
                    intro();
                    intro();
                    normalize();
                }
                have (to_integer(arena->capacity) - to_integer(i)) < at(region(13).entry, (to_integer(arena->capacity) - to_integer(i))) by {
                    rewrite(to_integer((at(iteration, i) + 1)) == (to_integer(at(iteration, i)) + 1));
                    normalize();
                }
            }
        }
    }
    let { lo: run_lo, hi: run_hi } = unfold(run);
    have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        have arena->occupied[k] == old(arena->occupied[k]) by {
            instantiate(forall (j: int32) { 0 <= j and j < arena->capacity implies arena->occupied[j] == at(find_first_free_run.entry, arena->occupied[j]) }, k) using {
                0 <= k;
                k < arena->capacity;
            };
        }
        instantiate(forall (j: int32) { at(find_first_free_run.entry, 0) <= at(find_first_free_run.entry, j) and at(find_first_free_run.entry, j) < at(find_first_free_run.entry, arena->capacity) implies at(find_first_free_run.entry, arena->occupied[j]) == old(arena->occupied[j]) }, k) using {
            0 <= k;
            k < arena->capacity;
        };
        rewrite(arena->occupied[k] == at(find_first_free_run.entry, arena->occupied[k]));
        assumption();
    }
    mark scanned;
    if at(region(17).entry, run_length) < at(region(17).entry, count) {
        step();
        fold(arena_cells(arena->data, arena->occupied, arena->capacity));
        step();
        let st = fold(arena_state(arena), { live: n, capacity: arena->capacity });
        let outcome = fold(arena_alloc_result(region), { model: ArenaAllocOutcome::Failure() });
        have result == 0 by {
            normalize();
        }
        have forall (k: int32) { result == 0 and 0 <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            extract(0 <= k);
            extract(k < arena->capacity);
            have arena->occupied[k] == old(arena->occupied[k]) by {
                instantiate(forall (j: int32) { at(scanned, 0) <= at(scanned, j) and at(scanned, j) < at(scanned, arena->capacity) implies at(scanned, arena->occupied[j]) == old(arena->occupied[j]) }, k) using {
                    0 <= k;
                    k < arena->capacity;
                };
            }
            transport(at(scanned, arena->occupied[k]) == old(arena->occupied[k]), arena->occupied[k] == old(arena->occupied[k])) using {
                at(scanned, arena->occupied[k]) == old(arena->occupied[k]);
                0 <= k;
                k < arena->capacity;
            };
        }
        assumption();
        have result == 0 or result == 1 by {
            assumption();
        }
        assumption();
        have to_integer(st.live) == (to_integer(old(st.live)) + to_integer(result)) by {
            normalize();
        }
        assumption();
        have arena->capacity == old(arena->capacity) by {
            normalize();
        }
        assumption();
        have arena->capacity <= 536870911 by {
            assumption();
        }
        assumption();
        have st.capacity == arena->capacity by {
            normalize();
        }
        assumption();
        have result == 0 implies outcome.model == ArenaAllocOutcome::Failure() by {
            intro();
            normalize();
        }
        assumption();
        have result == 1 implies outcome.model == ArenaAllocOutcome::Success(region->start, region->end) by {
            intro();
            contradiction(result == 1);
        }
        assumption();
        have result == 1 implies region->arena == arena by {
            intro();
            contradiction(result == 1);
        }
        assumption();
        have result == 1 implies to_integer(region->end) == (to_integer(region->start) + to_integer(count)) by {
            intro();
            contradiction(result == 1);
        }
        assumption();
        have result == 1 implies region->end <= arena->capacity by {
            intro();
            contradiction(result == 1);
        }
        assumption();
        have result == 1 implies 0 <= region->start by {
            intro();
            contradiction(result == 1);
        }
        assumption();
        have result == 1 implies region->start < region->end by {
            intro();
            contradiction(result == 1);
        }
        assumption();
        have forall (k: int32) { result == 1 and region->start <= k and k < region->end implies arena->occupied[k] == 1 } by {
            intro();
            intro();
            extract(result == 1);
            have not result == 1 by {
                normalize();
            }
            contradiction(result == 1);
        }
        assumption();
        have forall (k: int32) { result == 1 and 0 <= k and k < region->start implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            extract(result == 1);
            have not result == 1 by {
                normalize();
            }
            contradiction(result == 1);
        }
        assumption();
        have forall (k: int32) { result == 1 and region->end <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            extract(result == 1);
            have not result == 1 by {
                normalize();
            }
            contradiction(result == 1);
        }
        assumption();
        have forall (k: int32) { result == 1 and region->start <= k and k < region->end implies old(arena->occupied[k]) == 0 } by {
            intro();
            intro();
            extract(result == 1);
            have not result == 1 by {
                normalize();
            }
            contradiction(result == 1);
        }
        assumption();
        assumption();
        assumption();
    } else {
        step();
        step();
        have run_length == count by {
            extract(at(loop(0).exit, run_length) <= at(loop(0).exit, count));
            arithmetic_certificate {
                premise 0: at(loop(0).exit, run_length) <= at(loop(0).exit, count) =>
                    at(loop(0).exit, run_length) <= at(loop(0).exit, count);
                premise 1: not run_length < count => not run_length < count;
                equal_from_bounds 0, 1 => run_length == count;
                conclusion 2;
            }
        }
        have count == run_length by {
            assumption();
        }
        have (to_integer(run_lo) + to_integer(count)) == to_integer(i) by {
            assumption();
        }
        have 0 <= count by {
            assumption();
        }
        have defined((run_lo + count)) by {
            have (to_integer(run_lo) + to_integer(count)) >= -2147483648 by {
                arithmetic_certificate {
                    negated_goal => (to_integer(run_lo) + to_integer(count)) < -2147483648;
                    premise 0: 0 < to_integer(count) => 0 < to_integer(count);
                    premise 1: 0 <= to_integer(run_lo) => 0 <= to_integer(run_lo);
                    add 0, 1 => (to_integer(run_lo) + to_integer(count) + 1 + (0 + 1)) <=
                        (-2147483648 + to_integer(count));
                    add 3, 2 => (to_integer(run_lo) + to_integer(count) + 1 + (0 + 1) + 0) <=
                        (-2147483648 + to_integer(count) + to_integer(run_lo));
                    conclusion 4;
                }
            }
            have (to_integer(run_lo) + to_integer(count)) <= 2147483647 by {
                arithmetic_certificate {
                    negated_goal => 2147483647 < (to_integer(run_lo) + to_integer(count));
                    premise 0: to_integer(count) <= to_integer(at(region(7).entry, arena->capacity))
                        => to_integer(count) <= to_integer(at(region(7).entry, arena->capacity));
                    premise 1: to_integer(run_lo) <= to_integer(run_hi) => to_integer(run_lo) <=
                        to_integer(run_hi);
                    premise 2: to_integer(run_hi) <= to_integer(at(region(7).entry,
                        arena->capacity)) => to_integer(run_hi) <= to_integer(at(region(7).entry,
                        arena->capacity));
                    premise 3: to_integer(at(region(7).entry, arena->capacity)) <= 536870911 =>
                        to_integer(at(region(7).entry, arena->capacity)) <= 536870911;
                    scale 4 by 2 => (2 * to_integer(at(region(7).entry, arena->capacity))) <= (2 *
                        536870911);
                    add 0, 1 => (2147483647 + to_integer(count)) < (to_integer(run_lo) +
                        to_integer(count) + to_integer(at(region(7).entry, arena->capacity)));
                    add 6, 2 => (2147483647 + to_integer(count) + to_integer(run_lo)) <
                        (to_integer(run_lo) + to_integer(count) + to_integer(at(region(7).entry,
                        arena->capacity)) + to_integer(run_hi));
                    add 7, 3 => (2147483647 + to_integer(count) + to_integer(run_lo) +
                        to_integer(run_hi)) < (to_integer(run_lo) + to_integer(count) +
                        to_integer(at(region(7).entry, arena->capacity)) + to_integer(run_hi) +
                        to_integer(at(region(7).entry, arena->capacity)));
                    add 8, 5 => (2147483647 + to_integer(count) + to_integer(run_lo) +
                        to_integer(run_hi) + (2 * to_integer(at(region(7).entry, arena->capacity))))
                        < (to_integer(run_lo) + to_integer(count) + to_integer(at(region(7).entry,
                        arena->capacity)) + to_integer(run_hi) + to_integer(at(region(7).entry,
                        arena->capacity)) + (2 * 536870911));
                    conclusion 9;
                }
            }
            assumption();
        }
        have to_integer(count) <= (to_integer(run_lo) + to_integer(count)) by {
            arithmetic_certificate {
                negated_goal => (to_integer(run_lo) + to_integer(count)) < to_integer(count);
                premise 0: 0 <= to_integer(run_lo) => 0 <= to_integer(run_lo);
                add 0, 1 => (to_integer(run_lo) + to_integer(count) + 0) < (to_integer(count) +
                    to_integer(run_lo));
                conclusion 2;
            }
        }
        have to_integer(i) == (to_integer(run_lo) + to_integer(count)) by {
            assumption();
        }
        have count <= i by {
            assumption();
        }
        have defined((i - count)) by {
            extract(at(loop(0).exit, 0) <= at(loop(0).exit, run_length));
            extract(at(loop(0).exit, run_length) <= at(loop(0).exit, count));
            extract(at(function.entry, arena->capacity) <= at(function.entry, 1073741823));
            extract((let integer_value: Integer = to_integer((run_lo as int32)) + to_integer((count as int32)); integer_value) <= 2147483647);
            extract((let integer_value: Integer = to_integer((run_lo as int32)) + to_integer((count as int32)); integer_value) >= -2147483648);
            have to_integer(at(function.entry, i)) <= 2147483647 by {
                arithmetic_certificate {
                    type_range => to_integer(at(function.entry, i)) <= 2147483647;
                    conclusion 0;
                }
            }
            have -2147483648 <= (to_integer(at(function.entry, i)) - to_integer(at(function.entry, count))) by {
                arithmetic_certificate {
                    premise 0: at(function.entry, count) <= at(function.entry, i) =>
                        at(function.entry, count) <= at(function.entry, i);
                    trivial => -2147483648 <= 0;
                    add 0, 1 => (at(function.entry, to_integer((count as int32))) + -2147483648) <=
                        (at(function.entry, to_integer((i as int32))) + 0);
                    conclusion 2;
                }
            }
            have (to_integer(at(function.entry, i)) - to_integer(at(function.entry, count))) <= 2147483647 by {
                arithmetic_certificate {
                    premise 0: at(function.entry, 0) <= at(function.entry, count) =>
                        at(function.entry, 0) <= at(function.entry, count);
                    premise 1: to_integer(at(function.entry, i)) <= 2147483647 =>
                        to_integer(at(function.entry, i)) <= 2147483647;
                    add 0, 1 => (at(function.entry, 0) + to_integer(at(function.entry, i))) <=
                        (at(function.entry, to_integer((count as int32))) + 2147483647);
                    conclusion 2;
                }
            }
            assumption();
        }
        step();
        have to_integer((i - count)) == (to_integer(i) - to_integer(count)) by {
            have -2147483648 <= (to_integer(i) - to_integer(count)) by {
                assumption();
            }
            have (to_integer(i) - to_integer(count)) <= 2147483647 by {
                assumption();
            }
            have to_integer((i - count)) == (to_integer(i) - to_integer(count)) by {
                arithmetic_certificate rules {
                    premise 0: -2147483648 <= (to_integer(i) - to_integer(count)) => -2147483648 <=
                        (to_integer(i) - to_integer(count));
                    premise 1: (to_integer(i) - to_integer(count)) <= 2147483647 => (to_integer(i) -
                        to_integer(count)) <= 2147483647;
                    integer_operation_identity bounds [0, 1] => to_integer((i - count)) ==
                        (to_integer(i) - to_integer(count));
                    conclusion 0;
                }
            }
            assumption();
        }
        have to_integer(start) == to_integer(run_lo) by {
            rewrite(at(function.entry, to_integer(i)) == at(function.entry, (to_integer(run_lo) + to_integer(count))));
            normalize();
        }
        have start == run_lo by {
            assumption();
        }
        step();
        have end == i by {
            normalize();
        }
        have run_lo <= arena->capacity by {
            arithmetic_certificate {
                premise 0: run_lo <= run_hi => run_lo <= run_hi;
                premise 1: run_hi <= at(region(0).entry, arena->capacity) => run_hi <=
                    at(region(0).entry, arena->capacity);
                add 0, 1 => (to_integer((run_lo as int32)) + to_integer((run_hi as int32))) <=
                    (to_integer((run_hi as int32)) + at(region(0).entry, to_integer((arena->capacity
                    as int32))));
                conclusion 2;
            }
        }
        have start < end by {
            arithmetic_certificate signed_int32 {
                premise 0: (at(function.entry, 0) as int32) < (at(function.entry, count) as int32)
                    => (at(function.entry, 0) as int32) < (at(function.entry, count) as int32);
                premise 1: (at(function.entry, count) as int32) <= (at(function.entry, i) as int32)
                    => (at(function.entry, count) as int32) <= (at(function.entry, i) as int32);
                premise 2: (at(region(7).entry, count) as int32) <= (at(region(7).entry,
                    arena->capacity) as int32) => (at(region(7).entry, count) as int32) <=
                    (at(region(7).entry, arena->capacity) as int32);
                premise 3: (at(function.entry, arena->capacity) as int32) <= (at(function.entry,
                    536870911) as int32) => (at(function.entry, arena->capacity) as int32) <=
                    (at(function.entry, 536870911) as int32);
                add 1, 0 => (to_integer((at(function.entry, count) as int32)) +
                    to_integer((at(function.entry, 0) as int32))) < (to_integer((at(function.entry,
                    i) as int32)) + to_integer((at(function.entry, count) as int32)));
                interval_from_affine 4 (i) (1) (2147483647);
                add 2, 3 => (to_integer((at(region(7).entry, count) as int32)) +
                    to_integer((at(function.entry, arena->capacity) as int32))) <=
                    (to_integer((at(region(7).entry, arena->capacity) as int32)) +
                    to_integer((at(function.entry, 536870911) as int32)));
                interval_from_affine 0 (count) (1) (2147483647);
                interval_from_affine 6 (count) (-2147483648) (536870911);
                interval_intersect 7, 8 (1) (536870911);
                interval_subtract 5, 9 5 (-536870910) (2147483646);
                affine_conclusion 0 10 => (start as int32) < (end as int32);
                conclusion 11;
            }
        }
        have forall (k: int32) { start <= k and k < end implies arena->occupied[k] == 0 } by {
            rewrite(start == run_lo);
            rewrite(end == i);
            rewrite(at(loop(0).exit, i) == at(loop(0).exit, run.hi));
            assumption();
        }
        step();
        have i == start by {
            normalize();
        }
        have 0 <= start by {
            assumption();
        }
        have start <= end by {
            assumption();
        }
        have end <= arena->capacity by {
            assumption();
        }
        have forall (k: int32) { start <= k and k < start implies arena->occupied[k] == 1 } by {
            intro();
            intro();
            extract(start <= k);
            extract(k < start);
            have not k < start by {
                assumption();
            }
            contradiction(k < start);
        }
        have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            extract(0 <= k);
            extract(k < arena->capacity);
            have arena->occupied[k] == old(arena->occupied[k]) by {
                instantiate(forall (j: int32) { at(scanned, 0) <= at(scanned, j) and at(scanned, j) < at(scanned, arena->capacity) implies at(scanned, arena->occupied[j]) == old(arena->occupied[j]) }, k) using {
                    0 <= k;
                    k < arena->capacity;
                };
            }
            transport(at(scanned, arena->occupied[k]) == old(arena->occupied[k]), arena->occupied[k] == old(arena->occupied[k])) using {
                at(scanned, arena->occupied[k]) == old(arena->occupied[k]);
                0 <= k;
                k < arena->capacity;
            };
        }
        have forall (k: int32) { start <= k and k < end implies old(arena->occupied[k]) == 0 } by {
            intro();
            intro();
            extract(start <= k);
            extract(k < end);
            have 0 <= k by {
                arithmetic_certificate signed_int32 {
                    premise 0: (at(function.entry, 0) as int32) < (at(function.entry, count) as
                        int32) => (at(function.entry, 0) as int32) < (at(function.entry, count) as
                        int32);
                    premise 1: (at(function.entry, start) as int32) < (at(function.entry, end) as
                        int32) => (at(function.entry, start) as int32) < (at(function.entry, end) as
                        int32);
                    premise 2: (count as int32) <= (end as int32) => (count as int32) <= (end as
                        int32);
                    premise 3: (at(function.entry, end) as int32) <= (at(function.entry,
                        arena->capacity) as int32) => (at(function.entry, end) as int32) <=
                        (at(function.entry, arena->capacity) as int32);
                    premise 4: (at(function.entry, arena->capacity) as int32) <= (at(function.entry,
                        536870911) as int32) => (at(function.entry, arena->capacity) as int32) <=
                        (at(function.entry, 536870911) as int32);
                    premise 5: (at(function.entry, start) as int32) <= (at(function.entry, end) as
                        int32) => (at(function.entry, start) as int32) <= (at(function.entry, end)
                        as int32);
                    premise 6: (i as int32) <= (k as int32) => (i as int32) <= (k as int32);
                    add 2, 0 => (to_integer((count as int32)) + to_integer((at(function.entry, 0) as
                        int32))) < (to_integer((end as int32)) + to_integer((at(function.entry,
                        count) as int32)));
                    add 3, 4 => (to_integer((at(function.entry, end) as int32)) +
                        to_integer((at(function.entry, arena->capacity) as int32))) <=
                        (to_integer((at(function.entry, arena->capacity) as int32)) +
                        to_integer((at(function.entry, 536870911) as int32)));
                    interval_from_affine 7 (end) (1) (2147483647);
                    interval_from_affine 8 (end) (-2147483648) (536870911);
                    interval_intersect 9, 10 (1) (536870911);
                    add 2, 8 => (to_integer((count as int32)) + (to_integer((at(function.entry, end)
                        as int32)) + to_integer((at(function.entry, arena->capacity) as int32)))) <=
                        (to_integer((end as int32)) + (to_integer((at(function.entry,
                        arena->capacity) as int32)) + to_integer((at(function.entry, 536870911) as
                        int32))));
                    interval_from_affine 0 (count) (1) (2147483647);
                    interval_from_affine 12 (count) (-2147483648) (536870911);
                    interval_intersect 13, 14 (1) (536870911);
                    interval_subtract 11, 15 11 (-536870910) (536870910);
                    affine_premise 6 16 16 => to_integer((i as int32)) <= to_integer((k as int32));
                    add 2, 17 => 0 <= k;
                    conclusion 18;
                }
            }
            have k < arena->capacity by {
                arithmetic_certificate {
                    premise 0: k < end => k < end;
                    premise 1: at(function.entry, end) <= at(function.entry, arena->capacity) =>
                        at(function.entry, end) <= at(function.entry, arena->capacity);
                    add 0, 1 => (to_integer((k as int32)) + at(function.entry, to_integer((end as
                        int32)))) < (to_integer((end as int32)) + at(function.entry,
                        to_integer((arena->capacity as int32))));
                    conclusion 2;
                }
            }
            have old(arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) { start <= j and j < end implies arena->occupied[j] == 0 }, k) using {
                    start <= k;
                    k < end;
                };
            }
            instantiate(forall (j: int32) { 0 <= j and j < arena->capacity implies arena->occupied[j] == old(arena->occupied[j]) }, k) using {
                0 <= k;
                k < arena->capacity;
            };
            normalize() using {
                arena->occupied[k] == 0;
                arena->occupied[k] == old(arena->occupied[k]);
            };
        }
        have viewable(arena->occupied[0..arena->capacity]) by {
            transport(at(find_first_free_run.entry, viewable(arena->occupied[0..arena->capacity])), viewable(arena->occupied[0..arena->capacity])) using {
                at(find_first_free_run.entry, viewable(arena->occupied[0..arena->capacity]));
            };
        }
        let w = fold(arena_window(arena->data, arena->occupied, arena->capacity, start, end), { next: start });
        loop as mark_free_run {
            decreases (to_integer(end) - to_integer(i));
            owns w: arena_window(arena->data, arena->occupied, arena->capacity, start, end);
            invariant w.next == i;
            invariant forall (k: int32) { 0 <= k and k < start implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) };
            invariant forall (k: int32) { end <= k and k < arena->capacity implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) };
            invariant arena->data == old(arena->data);
            invariant arena->occupied == old(arena->occupied);
            initialize by {
                have w.next == i by {
                    normalize();
                }
                have forall (k: int32) { 0 <= k and k < start implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) } by {
                    intro();
                    intro();
                    normalize();
                }
                have forall (k: int32) { end <= k and k < arena->capacity implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) } by {
                    intro();
                    intro();
                    normalize();
                }
                have arena->data == old(arena->data) by {
                    normalize();
                }
                have arena->occupied == old(arena->occupied) by {
                    normalize();
                }
            }
            preserve by {
                let { next: m } = unfold(w);
                have m == i by {
                    assumption();
                }
                have m <= i by {
                    arithmetic_certificate signed_int32 {
                        premise 0: end == end => end == end;
                        premise 1: (at(region(24).entry, w.next) as int32) == (at(region(24).entry,
                            i) as int32) => (at(region(24).entry, w.next) as int32) ==
                            (at(region(24).entry, i) as int32);
                        less_equal_from_equal 0 => to_integer((end as int32)) <= to_integer((end as
                            int32));
                        less_equal_from_equal 1 => to_integer((at(region(24).entry, w.next) as
                            int32)) <= to_integer((at(region(24).entry, i) as int32));
                        add 2, 3 => (to_integer((end as int32)) + to_integer((at(region(24).entry,
                            w.next) as int32))) <= (to_integer((end as int32)) +
                            to_integer((at(region(24).entry, i) as int32)));
                        conclusion 4;
                    }
                }
                have i < end by {
                    assumption();
                }
                have end <= arena->capacity by {
                    assumption();
                }
                have arena->occupied[i] == 0 by {
                    instantiate(forall (k: int32) { m <= k and k < end implies arena->occupied[k] == 0 }, i) using {
                        m <= i;
                        i < end;
                    };
                }
                take(arena->data[i..(i + 1)]);
                have start <= i by {
                    assumption();
                }
                have 0 <= i by {
                    arithmetic_certificate signed_int32 {
                        premise 0: (at(function.entry, 0) as int32) < (at(function.entry, count) as
                            int32) => (at(function.entry, 0) as int32) < (at(function.entry, count)
                            as int32);
                        premise 1: (at(function.entry, start) as int32) < (at(function.entry, end)
                            as int32) => (at(function.entry, start) as int32) < (at(function.entry,
                            end) as int32);
                        premise 2: (count as int32) <= (end as int32) => (count as int32) <= (end as
                            int32);
                        premise 3: (at(function.entry, end) as int32) <= (at(function.entry,
                            arena->capacity) as int32) => (at(function.entry, end) as int32) <=
                            (at(function.entry, arena->capacity) as int32);
                        premise 4: (at(function.entry, arena->capacity) as int32) <=
                            (at(function.entry, 536870911) as int32) => (at(function.entry,
                            arena->capacity) as int32) <= (at(function.entry, 536870911) as int32);
                        premise 5: (at(function.entry, start) as int32) <= (at(function.entry, end)
                            as int32) => (at(function.entry, start) as int32) <= (at(function.entry,
                            end) as int32);
                        premise 6: (at(function.entry, start) as int32) <= (at(function.entry, i) as
                            int32) => (at(function.entry, start) as int32) <= (at(function.entry, i)
                            as int32);
                        premise 7: (start as int32) <= (m as int32) => (start as int32) <= (m as
                            int32);
                        add 2, 0 => (to_integer((count as int32)) + to_integer((at(function.entry,
                            0) as int32))) < (to_integer((end as int32)) +
                            to_integer((at(function.entry, count) as int32)));
                        add 3, 4 => (to_integer((at(function.entry, end) as int32)) +
                            to_integer((at(function.entry, arena->capacity) as int32))) <=
                            (to_integer((at(function.entry, arena->capacity) as int32)) +
                            to_integer((at(function.entry, 536870911) as int32)));
                        interval_from_affine 8 (end) (1) (2147483647);
                        interval_from_affine 9 (end) (-2147483648) (536870911);
                        interval_intersect 10, 11 (1) (536870911);
                        add 2, 9 => (to_integer((count as int32)) + (to_integer((at(function.entry,
                            end) as int32)) + to_integer((at(function.entry, arena->capacity) as
                            int32)))) <= (to_integer((end as int32)) +
                            (to_integer((at(function.entry, arena->capacity) as int32)) +
                            to_integer((at(function.entry, 536870911) as int32))));
                        interval_from_affine 0 (count) (1) (2147483647);
                        interval_from_affine 13 (count) (-2147483648) (536870911);
                        interval_intersect 14, 15 (1) (536870911);
                        interval_subtract 12, 16 12 (-536870910) (536870910);
                        affine_premise 6 17 17 => to_integer((at(function.entry, start) as int32))
                            <= to_integer((at(function.entry, i) as int32));
                        add 2, 18 => 0 <= i;
                        conclusion 19;
                    }
                }
                have i < arena->capacity by {
                    arithmetic_certificate {
                        premise 0: at(region(24).entry, i) < at(region(24).entry, end) =>
                            at(region(24).entry, i) < at(region(24).entry, end);
                        premise 1: at(function.entry, end) <= at(function.entry, arena->capacity) =>
                            at(function.entry, end) <= at(function.entry, arena->capacity);
                        add 0, 1 => (at(region(24).entry, to_integer((i as int32))) +
                            at(function.entry, to_integer((end as int32)))) < (at(region(24).entry,
                            to_integer((end as int32))) + at(function.entry,
                            to_integer((arena->capacity as int32))));
                        conclusion 2;
                    }
                }
                mark opened;
                have contains(memory(*arena), memory(arena->occupied)) by {
                    normalize();
                }
                have separate(memory(arena->occupied), memory(arena->occupied[i])) by {
                    apply(selected_array_cell(memory(*arena), memory(arena->occupied), arena->occupied, arena->capacity, i)) using {
                        separate(memory(*arena), memory(arena->occupied[0..arena->capacity]));
                        contains(memory(*arena), memory(arena->occupied));
                        0 <= i;
                        i < arena->capacity;
                    };
                }
                have contains(memory(*arena), memory(arena->data)) by {
                    normalize();
                }
                have separate(memory(arena->data), memory(arena->occupied[i])) by {
                    apply(selected_array_cell(memory(*arena), memory(arena->data), arena->occupied, arena->capacity, i)) using {
                        separate(memory(*arena), memory(arena->occupied[0..arena->capacity]));
                        contains(memory(*arena), memory(arena->data));
                        0 <= i;
                        i < arena->capacity;
                    };
                }
                have separate(memory(arena->occupied), memory(old(arena->occupied)[i])) by {
                    rewrite(old(arena->occupied) == arena->occupied);
                    assumption();
                }
                have separate(memory(arena->data), memory(old(arena->occupied)[i])) by {
                    rewrite(old(arena->occupied) == arena->occupied);
                    assumption();
                }
                step();
                have separate(statement(13).statement(0).footprint, memory(arena->occupied)) by {
                    normalize() using {
                        separate(memory(arena->occupied), memory(old(arena->occupied)[i]));
                    };
                }
                have arena->occupied == at(opened, arena->occupied) by {
                    transport_certificate {
                        premise 0: separate(statement(13).statement(0).footprint, memory(arena->occupied)) => separate(statement(13).statement(0).footprint, memory(arena->occupied));
                        preserve 0 => arena->occupied == at(opened, arena->occupied);
                        conclusion 1;
                    }
                }
                have arena->occupied == old(arena->occupied) by {
                    normalize() using {
                        arena->occupied == at(opened, arena->occupied);
                        at(opened, arena->occupied) == old(arena->occupied);
                    };
                }
                transport(at(opened, arena->capacity) == old(arena->capacity), arena->capacity == old(arena->capacity)) using {
                    at(opened, arena->capacity) == old(arena->capacity);
                    at(opened, separate(memory(*arena),
                        memory(arena->occupied[0..arena->capacity])));
                    0 <= at(opened, i);
                    at(opened, i) < at(opened, arena->capacity);
                };
                have separate(statement(13).statement(0).footprint, memory(arena->data)) by {
                    normalize() using {
                        separate(memory(arena->data), memory(old(arena->occupied)[i]));
                    };
                }
                have arena->data == at(opened, arena->data) by {
                    transport_certificate {
                        premise 0: separate(statement(13).statement(0).footprint, memory(arena->data)) => separate(statement(13).statement(0).footprint, memory(arena->data));
                        preserve 0 => arena->data == at(opened, arena->data);
                        conclusion 1;
                    }
                }
                have arena->data == old(arena->data) by {
                    normalize() using {
                        arena->data == at(opened, arena->data);
                        at(opened, arena->data) == old(arena->data);
                    };
                }
                have forall (k: int32) { (to_integer(at(opened, i)) + 1) <= to_integer(k) and k < end implies arena->occupied[k] == 0 } by {
                    intro();
                    intro();
                    extract((to_integer(at(opened, i)) + 1) <= to_integer(k));
                    extract(k < end);
                    have at(opened, i) < k by {
                        arithmetic_certificate {
                            negated_goal => to_integer((k as int32)) <= at(opened, to_integer((i as
                                int32)));
                            premise 0: (let integer_value: Integer = to_integer((i as int32)) + 1;
                                integer_value) <= to_integer((k as int32)) => (let integer_value:
                                Integer = to_integer((i as int32)) + 1; integer_value) <=
                                to_integer((k as int32));
                            add 0, 1 => (to_integer((k as int32)) + (let integer_value: Integer =
                                to_integer((i as int32)) + 1; integer_value)) <= (at(opened,
                                to_integer((i as int32))) + to_integer((k as int32)));
                            conclusion 2;
                        }
                    }
                    have at(opened, i) <= k by {
                        arithmetic_certificate {
                            premise 0: at(opened, i) < k => at(opened, i) < k;
                            trivial => -1 <= 0;
                            add 0, 1 => (at(opened, to_integer((i as int32))) + -1) < (to_integer((k
                                as int32)) + 0);
                            conclusion 2;
                        }
                    }
                    have m <= k by {
                        assumption();
                    }
                    have at(opened, arena->occupied[k]) == 0 by {
                        instantiate(forall (j: int32) { at(opened, m) <= at(opened, j) and at(opened, j) < at(opened, end) implies at(opened, arena->occupied[j]) == at(opened, 0) }, k) using {
                            m <= k;
                            k < end;
                        };
                    }
                    have 0 <= k by {
                        arithmetic_certificate signed_int32 {
                            premise 0: (at(function.entry, 0) as int32) <= (at(function.entry, i) as
                                int32) => (at(function.entry, 0) as int32) <= (at(function.entry, i)
                                as int32);
                            premise 1: (at(opened, i) as int32) <= (k as int32) => (at(opened, i) as
                                int32) <= (k as int32);
                            add 0, 1 => (to_integer((at(function.entry, 0) as int32)) +
                                to_integer((at(opened, i) as int32))) <=
                                (to_integer((at(function.entry, i) as int32)) + to_integer((k as
                                int32)));
                            conclusion 2;
                        }
                    }
                    have k < at(opened, arena->capacity) by {
                        arithmetic_certificate {
                            premise 0: k < end => k < end;
                            premise 1: at(function.entry, end) <= at(function.entry,
                                arena->capacity) => at(function.entry, end) <= at(function.entry,
                                arena->capacity);
                            add 0, 1 => (to_integer((k as int32)) + at(function.entry,
                                to_integer((end as int32)))) < (to_integer((end as int32)) +
                                at(function.entry, to_integer((arena->capacity as int32))));
                            conclusion 2;
                        }
                    }
                    transport(at(opened, arena->occupied[k]) == 0, arena->occupied[k] == 0) using {
                        at(opened, arena->occupied) == old(arena->occupied);
                        arena->occupied == old(arena->occupied);
                        at(opened, separate(memory(*arena),
                            memory(arena->occupied[0..arena->capacity])));
                        at(opened, separate(memory(*arena),
                            memory(arena->data[0..arena->capacity])));
                        at(opened, arena->occupied[k]) == 0;
                        at(opened, i) < k;
                        0 <= at(opened, i);
                        at(opened, i) < at(opened, arena->capacity);
                        0 <= k;
                        k < at(opened, arena->capacity);
                    };
                }
                have forall (k: int32) { start <= k and to_integer(k) < (to_integer(at(opened, i)) + 1) implies arena->occupied[k] == 1 } by {
                    intro();
                    intro();
                    extract(start <= k);
                    extract(to_integer(k) < (to_integer(at(opened, i)) + 1));
                    if k < at(opened, i) {
                        have k < m by {
                            assumption();
                        }
                        have at(opened, arena->occupied[k]) == 1 by {
                            instantiate(forall (j: int32) { at(opened, start) <= at(opened, j) and at(opened, j) < at(opened, m) implies at(opened, arena->occupied[j]) == at(opened, 1) }, k) using {
                                start <= k;
                                k < m;
                            };
                        }
                        have 0 <= k by {
                            arithmetic_certificate signed_int32 {
                                premise 0: (at(function.entry, 0) as int32) < (at(function.entry,
                                    count) as int32) => (at(function.entry, 0) as int32) <
                                    (at(function.entry, count) as int32);
                                premise 1: (at(region(24).entry, i) as int32) <
                                    (at(region(24).entry, end) as int32) => (at(region(24).entry, i)
                                    as int32) < (at(region(24).entry, end) as int32);
                                premise 2: (at(function.entry, start) as int32) <
                                    (at(function.entry, end) as int32) => (at(function.entry, start)
                                    as int32) < (at(function.entry, end) as int32);
                                premise 3: (at(function.entry, 0) as int32) <= (at(function.entry,
                                    i) as int32) => (at(function.entry, 0) as int32) <=
                                    (at(function.entry, i) as int32);
                                premise 4: (count as int32) <= (end as int32) => (count as int32) <=
                                    (end as int32);
                                premise 5: (at(function.entry, end) as int32) <= (at(function.entry,
                                    arena->capacity) as int32) => (at(function.entry, end) as int32)
                                    <= (at(function.entry, arena->capacity) as int32);
                                premise 6: (at(function.entry, arena->capacity) as int32) <=
                                    (at(function.entry, 536870911) as int32) => (at(function.entry,
                                    arena->capacity) as int32) <= (at(function.entry, 536870911) as
                                    int32);
                                premise 7: (at(function.entry, start) as int32) <=
                                    (at(function.entry, end) as int32) => (at(function.entry, start)
                                    as int32) <= (at(function.entry, end) as int32);
                                premise 8: (at(function.entry, start) as int32) <=
                                    (at(function.entry, i) as int32) => (at(function.entry, start)
                                    as int32) <= (at(function.entry, i) as int32);
                                premise 9: (start as int32) <= (m as int32) => (start as int32) <=
                                    (m as int32);
                                premise 10: (start as int32) <= (k as int32) => (start as int32) <=
                                    (k as int32);
                                add 1, 3 => (to_integer((at(region(24).entry, i) as int32)) +
                                    to_integer((at(function.entry, 0) as int32))) <
                                    (to_integer((at(region(24).entry, end) as int32)) +
                                    to_integer((at(function.entry, i) as int32)));
                                add 5, 6 => (to_integer((at(function.entry, end) as int32)) +
                                    to_integer((at(function.entry, arena->capacity) as int32))) <=
                                    (to_integer((at(function.entry, arena->capacity) as int32)) +
                                    to_integer((at(function.entry, 536870911) as int32)));
                                interval_from_affine 11 (end) (1) (2147483647);
                                interval_from_affine 12 (end) (-2147483648) (536870911);
                                interval_intersect 13, 14 (1) (536870911);
                                add 4, 12 => (to_integer((count as int32)) +
                                    (to_integer((at(function.entry, end) as int32)) +
                                    to_integer((at(function.entry, arena->capacity) as int32)))) <=
                                    (to_integer((end as int32)) + (to_integer((at(function.entry,
                                    arena->capacity) as int32)) + to_integer((at(function.entry,
                                    536870911) as int32))));
                                interval_from_affine 0 (count) (1) (2147483647);
                                interval_from_affine 16 (count) (-2147483648) (536870911);
                                interval_intersect 17, 18 (1) (536870911);
                                interval_subtract 15, 19 15 (-536870910) (536870910);
                                affine_premise 10 20 20 => to_integer((start as int32)) <=
                                    to_integer((k as int32));
                                add 4, 21 => 0 <= k;
                                conclusion 22;
                            }
                        }
                        transport(at(opened, arena->occupied[k]) == 1, arena->occupied[k] == 1) using {
                            at(opened, arena->occupied[k]) == 1;
                            k < at(opened, i);
                            0 <= k;
                            0 <= at(opened, i);
                            at(opened, i) < arena->capacity;
                        };
                    } else {
                        have k <= at(opened, i) by {
                            arithmetic_certificate {
                                negated_goal => at(opened, to_integer((i as int32))) < to_integer((k
                                    as int32));
                                premise 0: (let integer_value: Integer = to_integer((k as int32));
                                    integer_value) < (to_integer((i as int32)) + 1) => (let
                                    integer_value: Integer = to_integer((k as int32));
                                    integer_value) < (to_integer((i as int32)) + 1);
                                add 0, 1 => (at(opened, to_integer((i as int32))) + 1 + ((let
                                    integer_value: Integer = to_integer((k as int32));
                                    integer_value) + 1)) <= (to_integer((k as int32)) +
                                    (to_integer((i as int32)) + 1));
                                conclusion 2;
                            }
                        }
                        have k == at(opened, i) by {
                            arithmetic_certificate {
                                premise 0: k <= at(opened, i) => k <= at(opened, i);
                                premise 1: not k < i => not k < i;
                                equal_from_bounds 0, 1 => k == at(opened, i);
                                conclusion 2;
                            }
                        }
                        rewrite(k == at(opened, i));
                        normalize() using {
                            arena->occupied == old(arena->occupied);
                        };
                    }
                }
                step();
                have forall (k: int32) { 0 <= k and k < start implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) } by {
                    intro();
                    intro();
                    extract(0 <= k);
                    extract(k < start);
                    have at(opened, arena->occupied[k]) == at(mark_free_run.entry, arena->occupied[k]) by {
                        instantiate(forall (j: int32) { at(opened, 0) <= at(opened, j) and at(opened, j) < at(opened, start) implies at(opened, arena->occupied[j]) == at(mark_free_run.entry, arena->occupied[j]) }, k) using {
                            0 <= k;
                            k < start;
                        };
                    }
                    have k < at(opened, i) by {
                        arithmetic_certificate {
                            premise 0: k < start => k < start;
                            premise 1: start <= at(region(24).entry, i) => start <=
                                at(region(24).entry, i);
                            add 0, 1 => (to_integer((k as int32)) + to_integer((start as int32))) <
                                (to_integer((start as int32)) + at(region(24).entry, to_integer((i
                                as int32))));
                            conclusion 2;
                        }
                    }
                    transport(at(opened, arena->occupied[k]) == at(mark_free_run.entry, arena->occupied[k]), arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k])) using {
                        at(opened, arena->occupied[k]) == at(mark_free_run.entry,
                            arena->occupied[k]);
                        k < at(opened, i);
                        0 <= k;
                        0 <= at(opened, i);
                        at(opened, i) < arena->capacity;
                    };
                }
                have forall (k: int32) { end <= k and k < arena->capacity implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) } by {
                    intro();
                    intro();
                    extract(end <= k);
                    extract(k < arena->capacity);
                    have k < at(opened, arena->capacity) by {
                        assumption();
                    }
                    have at(opened, arena->occupied[k]) == at(mark_free_run.entry, arena->occupied[k]) by {
                        instantiate(forall (j: int32) { at(opened, end) <= at(opened, j) and at(opened, j) < at(opened, arena->capacity) implies at(opened, arena->occupied[j]) == at(mark_free_run.entry, arena->occupied[j]) }, k) using {
                            end <= k;
                            k < at(opened, arena->capacity);
                        };
                    }
                    have at(opened, i) < k by {
                        arithmetic_certificate {
                            premise 0: at(region(24).entry, i) < at(region(24).entry, end) =>
                                at(region(24).entry, i) < at(region(24).entry, end);
                            premise 1: end <= k => end <= k;
                            add 0, 1 => (at(region(24).entry, to_integer((i as int32))) +
                                to_integer((end as int32))) < (at(region(24).entry, to_integer((end
                                as int32))) + to_integer((k as int32)));
                            conclusion 2;
                        }
                    }
                    have at(opened, i) <= k by {
                        arithmetic_certificate signed_int32 {
                            premise 0: (at(opened, i) as int32) < (k as int32) => (at(opened, i) as
                                int32) < (k as int32);
                            trivial => -1 <= 0;
                            add 0, 1 => (to_integer((at(opened, i) as int32)) + -1) < (to_integer((k
                                as int32)) + 0);
                            conclusion 2;
                        }
                    }
                    have 0 <= k by {
                        arithmetic_certificate signed_int32 {
                            premise 0: (0 as int32) <= (at(region(24).entry, i) as int32) => (0 as
                                int32) <= (at(region(24).entry, i) as int32);
                            premise 1: (at(opened, i) as int32) <= (k as int32) => (at(opened, i) as
                                int32) <= (k as int32);
                            add 0, 1 => (to_integer((0 as int32)) + to_integer((at(opened, i) as
                                int32))) <= (to_integer((at(region(24).entry, i) as int32)) +
                                to_integer((k as int32)));
                            conclusion 2;
                        }
                    }
                    transport(at(opened, arena->occupied[k]) == at(mark_free_run.entry, arena->occupied[k]), arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k])) using {
                        at(opened, arena->occupied[k]) == at(mark_free_run.entry,
                            arena->occupied[k]);
                        at(opened, i) < k;
                        0 <= at(opened, i);
                        at(opened, i) < arena->capacity;
                        0 <= k;
                        k < arena->capacity;
                    };
                }
                have forall (k: int32) { i <= k and k < end implies arena->occupied[k] == 0 } by {
                    intro();
                    intro();
                    extract(i <= k);
                    extract(k < end);
                    have (to_integer(at(opened, i)) + 1) <= to_integer(k) by {
                        have -2147483648 <= (to_integer(at(opened, i)) + 1) by {
                            arithmetic_certificate {
                                negated_goal => (to_integer(at(opened, i)) + 1) < -2147483648;
                                premise 0: 0 <= to_integer(at(opened, i)) => 0 <=
                                    to_integer(at(opened, i));
                                add 0, 1 => (to_integer(at(opened, i)) + 1 + 0) < (-2147483648 +
                                    to_integer(at(opened, i)));
                                conclusion 2;
                            }
                        }
                        have (to_integer(at(opened, i)) + 1) <= 2147483647 by {
                            arithmetic_certificate {
                                negated_goal => 2147483647 < (to_integer(at(opened, i)) + 1);
                                premise 0: (let integer_value: Integer = to_integer((run_lo as
                                    int32)) + to_integer((count as int32)); integer_value) <=
                                    2147483647 => (let integer_value: Integer = to_integer((run_lo
                                    as int32)) + to_integer((count as int32)); integer_value) <=
                                    2147483647;
                                premise 1: (let integer_value: Integer = to_integer((end as int32));
                                    integer_value) == (to_integer((run_lo as int32)) +
                                    to_integer((count as int32))) => (let integer_value: Integer =
                                    to_integer((end as int32)); integer_value) ==
                                    (to_integer((run_lo as int32)) + to_integer((count as int32)));
                                less_equal_from_equal 2 => (let integer_value: Integer =
                                    to_integer((end as int32)); integer_value) <=
                                    (to_integer((run_lo as int32)) + to_integer((count as int32)));
                                premise 2: to_integer(at(opened, i)) < to_integer((let
                                    integer_value: Integer = to_integer((end as int32));
                                    integer_value)) => to_integer(at(opened, i)) < to_integer((let
                                    integer_value: Integer = to_integer((end as int32));
                                    integer_value));
                                add 0, 1 => (2147483647 + (let integer_value: Integer =
                                    to_integer((run_lo as int32)) + to_integer((count as int32));
                                    integer_value)) < (to_integer(at(opened, i)) + 1 + 2147483647);
                                add 5, 3 => (2147483647 + (let integer_value: Integer =
                                    to_integer((run_lo as int32)) + to_integer((count as int32));
                                    integer_value) + (let integer_value: Integer = to_integer((end
                                    as int32)); integer_value)) < (to_integer(at(opened, i)) + 1 +
                                    2147483647 + (to_integer((run_lo as int32)) + to_integer((count
                                    as int32))));
                                add 6, 4 => (2147483647 + (let integer_value: Integer =
                                    to_integer((run_lo as int32)) + to_integer((count as int32));
                                    integer_value) + (let integer_value: Integer = to_integer((end
                                    as int32)); integer_value) + 1 + (to_integer(at(opened, i)) +
                                    1)) <= (to_integer(at(opened, i)) + 1 + 2147483647 +
                                    (to_integer((run_lo as int32)) + to_integer((count as int32))) +
                                    to_integer((let integer_value: Integer = to_integer((end as
                                    int32)); integer_value)));
                                conclusion 7;
                            }
                        }
                        have to_integer((i as int32)) == (to_integer(at(opened, i)) + 1) by {
                            arithmetic_certificate rules {
                                premise 0: -2147483648 <= (to_integer(at(opened, i)) + 1) =>
                                    -2147483648 <= (to_integer(at(opened, i)) + 1);
                                premise 1: (to_integer(at(opened, i)) + 1) <= 2147483647 =>
                                    (to_integer(at(opened, i)) + 1) <= 2147483647;
                                integer_operation_identity bounds [0, 1] => to_integer((i as int32))
                                    == (to_integer(at(opened, i)) + 1);
                                conclusion 0;
                            }
                        }
                        arithmetic_certificate {
                            negated_goal => to_integer(k) < (to_integer(at(opened, i)) + 1);
                            premise 0: to_integer((i as int32)) == (to_integer(at(opened, i)) + 1)
                                => to_integer((i as int32)) == (to_integer(at(opened, i)) + 1);
                            less_equal_from_equal 1 reverse => (to_integer(at(opened, i)) + 1) <=
                                to_integer((i as int32));
                            premise 1: to_integer((i as int32)) <= to_integer(k) => to_integer((i as
                                int32)) <= to_integer(k);
                            add 0, 2 => (to_integer(k) + (to_integer(at(opened, i)) + 1)) <
                                (to_integer(at(opened, i)) + 1 + to_integer((i as int32)));
                            add 4, 3 => (to_integer(k) + (to_integer(at(opened, i)) + 1) +
                                to_integer((i as int32))) < (to_integer(at(opened, i)) + 1 +
                                to_integer((i as int32)) + to_integer(k));
                            conclusion 5;
                        }
                    }
                    instantiate(forall (j: int32) { (to_integer(at(opened, i)) + 1) <= to_integer(j) and j < end implies arena->occupied[j] == 0 }, k) using {
                        (to_integer(at(opened, i)) + 1) <= to_integer(k);
                        k < end;
                    };
                }
                have forall (k: int32) { start <= k and k < i implies arena->occupied[k] == 1 } by {
                    intro();
                    intro();
                    extract(start <= k);
                    extract(k < i);
                    have to_integer(k) < (to_integer(at(opened, i)) + 1) by {
                        have -2147483648 <= (to_integer(at(opened, i)) + 1) by {
                            arithmetic_certificate {
                                negated_goal => (to_integer(at(opened, i)) + 1) < -2147483648;
                                premise 0: 0 <= to_integer(at(opened, i)) => 0 <=
                                    to_integer(at(opened, i));
                                add 0, 1 => (to_integer(at(opened, i)) + 1 + 0) < (-2147483648 +
                                    to_integer(at(opened, i)));
                                conclusion 2;
                            }
                        }
                        have (to_integer(at(opened, i)) + 1) <= 2147483647 by {
                            arithmetic_certificate {
                                negated_goal => 2147483647 < (to_integer(at(opened, i)) + 1);
                                premise 0: (let integer_value: Integer = to_integer((run_lo as
                                    int32)) + to_integer((count as int32)); integer_value) <=
                                    2147483647 => (let integer_value: Integer = to_integer((run_lo
                                    as int32)) + to_integer((count as int32)); integer_value) <=
                                    2147483647;
                                premise 1: (let integer_value: Integer = to_integer((end as int32));
                                    integer_value) == (to_integer((run_lo as int32)) +
                                    to_integer((count as int32))) => (let integer_value: Integer =
                                    to_integer((end as int32)); integer_value) ==
                                    (to_integer((run_lo as int32)) + to_integer((count as int32)));
                                less_equal_from_equal 2 => (let integer_value: Integer =
                                    to_integer((end as int32)); integer_value) <=
                                    (to_integer((run_lo as int32)) + to_integer((count as int32)));
                                premise 2: to_integer(at(opened, i)) < to_integer((let
                                    integer_value: Integer = to_integer((end as int32));
                                    integer_value)) => to_integer(at(opened, i)) < to_integer((let
                                    integer_value: Integer = to_integer((end as int32));
                                    integer_value));
                                add 0, 1 => (2147483647 + (let integer_value: Integer =
                                    to_integer((run_lo as int32)) + to_integer((count as int32));
                                    integer_value)) < (to_integer(at(opened, i)) + 1 + 2147483647);
                                add 5, 3 => (2147483647 + (let integer_value: Integer =
                                    to_integer((run_lo as int32)) + to_integer((count as int32));
                                    integer_value) + (let integer_value: Integer = to_integer((end
                                    as int32)); integer_value)) < (to_integer(at(opened, i)) + 1 +
                                    2147483647 + (to_integer((run_lo as int32)) + to_integer((count
                                    as int32))));
                                add 6, 4 => (2147483647 + (let integer_value: Integer =
                                    to_integer((run_lo as int32)) + to_integer((count as int32));
                                    integer_value) + (let integer_value: Integer = to_integer((end
                                    as int32)); integer_value) + 1 + (to_integer(at(opened, i)) +
                                    1)) <= (to_integer(at(opened, i)) + 1 + 2147483647 +
                                    (to_integer((run_lo as int32)) + to_integer((count as int32))) +
                                    to_integer((let integer_value: Integer = to_integer((end as
                                    int32)); integer_value)));
                                conclusion 7;
                            }
                        }
                        have to_integer((i as int32)) == (to_integer(at(opened, i)) + 1) by {
                            arithmetic_certificate rules {
                                premise 0: -2147483648 <= (to_integer(at(opened, i)) + 1) =>
                                    -2147483648 <= (to_integer(at(opened, i)) + 1);
                                premise 1: (to_integer(at(opened, i)) + 1) <= 2147483647 =>
                                    (to_integer(at(opened, i)) + 1) <= 2147483647;
                                integer_operation_identity bounds [0, 1] => to_integer((i as int32))
                                    == (to_integer(at(opened, i)) + 1);
                                conclusion 0;
                            }
                        }
                        arithmetic_certificate {
                            negated_goal => (to_integer(at(opened, i)) + 1) <= to_integer(k);
                            premise 0: to_integer((i as int32)) == (to_integer(at(opened, i)) + 1)
                                => to_integer((i as int32)) == (to_integer(at(opened, i)) + 1);
                            less_equal_from_equal 1 => to_integer((i as int32)) <=
                                (to_integer(at(opened, i)) + 1);
                            premise 1: to_integer(k) < to_integer((i as int32)) => to_integer(k) <
                                to_integer((i as int32));
                            add 0, 2 => (to_integer(at(opened, i)) + 1 + to_integer((i as int32)))
                                <= (to_integer(k) + (to_integer(at(opened, i)) + 1));
                            add 4, 3 => (to_integer(at(opened, i)) + 1 + to_integer((i as int32)) +
                                to_integer(k)) < (to_integer(k) + (to_integer(at(opened, i)) + 1) +
                                to_integer((i as int32)));
                            conclusion 5;
                        }
                    }
                    instantiate(forall (j: int32) { start <= j and to_integer(j) < (to_integer(at(opened, i)) + 1) implies arena->occupied[j] == 1 }, k) using {
                        start <= k;
                        to_integer(k) < (to_integer(at(opened, i)) + 1);
                    };
                }
                transport(at(opened, viewable(arena->occupied[0..arena->capacity])), viewable(arena->occupied[0..arena->capacity])) using {
                    at(opened, viewable(arena->occupied[0..arena->capacity]));
                    at(opened, arena->occupied) == old(arena->occupied);
                    arena->occupied == old(arena->occupied);
                    at(opened, arena->capacity) == old(arena->capacity);
                    arena->capacity == old(arena->capacity);
                };
                have forall (k: int32) { i <= k and k < end implies load_int32((old(arena->occupied) + k)) == 0 } by {
                    intro();
                    intro();
                    instantiate(forall (j: int32) { i <= j and j < end implies arena->occupied[j] == 0 }, k) using { i <= k and k < end; };
                    have &arena->occupied[k] == old(&arena->occupied[k]) by {
                        normalize() using { old(arena->occupied) == arena->occupied; };
                    }
                    normalize() using {
                        arena->occupied[k] == 0;
                        &arena->occupied[k] == old(&arena->occupied[k]);
                    };
                }
                have forall (k: int32) { start <= k and k < i implies load_int32((old(arena->occupied) + k)) == 1 } by {
                    intro();
                    intro();
                    instantiate(forall (j: int32) { start <= j and j < i implies arena->occupied[j] == 1 }, k) using { start <= k and k < i; };
                    have &arena->occupied[k] == old(&arena->occupied[k]) by {
                        normalize() using { old(arena->occupied) == arena->occupied; };
                    }
                    normalize() using {
                        arena->occupied[k] == 1;
                        &arena->occupied[k] == old(&arena->occupied[k]);
                    };
                }
                have to_integer(i) == (to_integer(at(opened, i)) + 1) by {
                    have -2147483648 <= (to_integer(at(opened, i)) + 1) by {
                        arithmetic_certificate {
                            negated_goal => (to_integer(at(opened, i)) + 1) < -2147483648;
                            premise 0: 0 <= to_integer(at(opened, i)) => 0 <= to_integer(at(opened,
                                i));
                            add 0, 1 => (to_integer(at(opened, i)) + 1 + 0) < (-2147483648 +
                                to_integer(at(opened, i)));
                            conclusion 2;
                        }
                    }
                    have (to_integer(at(opened, i)) + 1) <= 2147483647 by {
                        arithmetic_certificate {
                            negated_goal => 2147483647 < (to_integer(at(opened, i)) + 1);
                            premise 0: (let integer_value: Integer = to_integer((run_lo as int32)) +
                                to_integer((count as int32)); integer_value) <= 2147483647 => (let
                                integer_value: Integer = to_integer((run_lo as int32)) +
                                to_integer((count as int32)); integer_value) <= 2147483647;
                            premise 1: (let integer_value: Integer = to_integer((end as int32));
                                integer_value) == (to_integer((run_lo as int32)) + to_integer((count
                                as int32))) => (let integer_value: Integer = to_integer((end as
                                int32)); integer_value) == (to_integer((run_lo as int32)) +
                                to_integer((count as int32)));
                            less_equal_from_equal 2 => (let integer_value: Integer = to_integer((end
                                as int32)); integer_value) <= (to_integer((run_lo as int32)) +
                                to_integer((count as int32)));
                            premise 2: to_integer(at(opened, i)) < to_integer((let integer_value:
                                Integer = to_integer((end as int32)); integer_value)) =>
                                to_integer(at(opened, i)) < to_integer((let integer_value: Integer =
                                to_integer((end as int32)); integer_value));
                            add 0, 1 => (2147483647 + (let integer_value: Integer =
                                to_integer((run_lo as int32)) + to_integer((count as int32));
                                integer_value)) < (to_integer(at(opened, i)) + 1 + 2147483647);
                            add 5, 3 => (2147483647 + (let integer_value: Integer =
                                to_integer((run_lo as int32)) + to_integer((count as int32));
                                integer_value) + (let integer_value: Integer = to_integer((end as
                                int32)); integer_value)) < (to_integer(at(opened, i)) + 1 +
                                2147483647 + (to_integer((run_lo as int32)) + to_integer((count as
                                int32))));
                            add 6, 4 => (2147483647 + (let integer_value: Integer =
                                to_integer((run_lo as int32)) + to_integer((count as int32));
                                integer_value) + (let integer_value: Integer = to_integer((end as
                                int32)); integer_value) + 1 + (to_integer(at(opened, i)) + 1)) <=
                                (to_integer(at(opened, i)) + 1 + 2147483647 + (to_integer((run_lo as
                                int32)) + to_integer((count as int32))) + to_integer((let
                                integer_value: Integer = to_integer((end as int32));
                                integer_value)));
                            conclusion 7;
                        }
                    }
                    have to_integer(i) == (to_integer(at(opened, i)) + 1) by {
                        arithmetic_certificate rules {
                            premise 0: -2147483648 <= (to_integer(at(opened, i)) + 1) => -2147483648
                                <= (to_integer(at(opened, i)) + 1);
                            premise 1: (to_integer(at(opened, i)) + 1) <= 2147483647 =>
                                (to_integer(at(opened, i)) + 1) <= 2147483647;
                            integer_operation_identity bounds [0, 1] => to_integer(i) ==
                                (to_integer(at(opened, i)) + 1);
                            conclusion 0;
                        }
                    }
                    assumption();
                }
                have start <= i by {
                    solve() using { start <= at(opened, i); to_integer(i) == to_integer(at(opened, i)) + 1; };
                }
                have i <= end by {
                    solve() using { at(opened, i) < end; to_integer(i) == to_integer(at(opened, i)) + 1; };
                }
                let w = fold(arena_window(old(arena->data), old(arena->occupied), old(arena->capacity), start, end), { next: i });
                have 0 <= (to_integer(end) - to_integer(i)) by {
                    arithmetic_certificate {
                        premise 0: to_integer(i) <= to_integer(end) => 0 <= (to_integer(end) -
                            to_integer(i));
                        conclusion 0;
                    }
                }
                have (to_integer(end) - to_integer(i)) < (to_integer(end) - to_integer(at(opened, i))) by {
                    rewrite(to_integer(i) == (to_integer(at(opened, i)) + 1));
                    normalize();
                }
                have w.next == i by {
                    normalize();
                }
                have w.next == i implies forall (k: int32) { 0 <= k and k < start implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) } by {
                    intro();
                    assumption();
                }
                have w.next == i implies forall (k: int32) { 0 <= k and k < start implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) } implies forall (k: int32) { end <= k and k < arena->capacity implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) } by {
                    intro();
                    intro();
                    assumption();
                }
                have w.next == i implies forall (k: int32) { 0 <= k and k < start implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) } implies forall (k: int32) { end <= k and k < arena->capacity implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) } implies arena->data == old(arena->data) by {
                    intro();
                    intro();
                    intro();
                    assumption();
                }
                have w.next == i implies forall (k: int32) { 0 <= k and k < start implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) } implies forall (k: int32) { end <= k and k < arena->capacity implies arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]) } implies arena->data == old(arena->data) implies arena->occupied == old(arena->occupied) by {
                    intro();
                    intro();
                    intro();
                    intro();
                    assumption();
                }
            }
        }
        let { next: m } = unfold(w);
        have m <= end by {
            assumption();
        }
        have m == i by {
            assumption();
        }
        have not m < end by {
            assumption();
        }
        have m == end by {
            arithmetic_certificate {
                premise 0: at(function.entry, m) <= at(function.entry, end) => at(function.entry, m)
                    <= at(function.entry, end);
                premise 1: not at(function.entry, m) < at(function.entry, end) => not
                    at(function.entry, m) < at(function.entry, end);
                equal_from_bounds 0, 1 => m == end;
                conclusion 2;
            }
        }
        have forall (k: int32) { start <= k and k < end implies arena->occupied[k] == 1 } by {
            intro();
            intro();
            extract(start <= k);
            extract(k < end);
            have k < m by {
                assumption();
            }
            instantiate(forall (j: int32) { start <= j and j < m implies arena->occupied[j] == 1 }, k) using {
                start <= k;
                k < m;
            };
        }
        have forall (k: int32) { 0 <= k and k < start implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            extract(0 <= k);
            extract(k < start);
            have arena->occupied[k] == old(arena->occupied[k]) by {
                instantiate(forall (j: int32) { 0 <= j and j < start implies arena->occupied[j] == at(mark_free_run.entry, arena->occupied[j]) }, k) using {
                    0 <= k;
                    k < start;
                };
            }
            have k < end by {
                arithmetic_certificate {
                    premise 0: k < start => k < start;
                    premise 1: at(function.entry, start) < at(function.entry, end) =>
                        at(function.entry, start) < at(function.entry, end);
                    add 0, 1 => (to_integer((k as int32)) + 1 + (at(function.entry,
                        to_integer((start as int32))) + 1)) <= (to_integer((start as int32)) +
                        at(function.entry, to_integer((end as int32))));
                    trivial => -1 <= 0;
                    add 2, 3 => (to_integer((k as int32)) + 1 + (at(function.entry,
                        to_integer((start as int32))) + 1) + -1) <= (to_integer((start as int32)) +
                        at(function.entry, to_integer((end as int32))) + 0);
                    conclusion 4;
                }
            }
            have k < arena->capacity by {
                arithmetic_certificate {
                    premise 0: at(function.entry, k) < at(function.entry, end) => at(function.entry,
                        k) < at(function.entry, end);
                    premise 1: at(function.entry, end) <= at(function.entry, arena->capacity) =>
                        at(function.entry, end) <= at(function.entry, arena->capacity);
                    add 0, 1 => (at(function.entry, to_integer((k as int32))) + at(function.entry,
                        to_integer((end as int32)))) < (at(function.entry, to_integer((end as
                        int32))) + at(function.entry, to_integer((arena->capacity as int32))));
                    conclusion 2;
                }
            }
            instantiate(forall (j: int32) { at(mark_free_run.entry, 0) <= at(mark_free_run.entry, j) and at(mark_free_run.entry, j) < at(mark_free_run.entry, arena->capacity) implies at(mark_free_run.entry, arena->occupied[j]) == old(arena->occupied[j]) }, k) using {
                0 <= k;
                k < arena->capacity;
            };
            normalize() using {
                arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]);
                at(mark_free_run.entry, arena->occupied[k]) == old(arena->occupied[k]);
            };
        }
        have forall (k: int32) { end <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            extract(end <= k);
            extract(k < arena->capacity);
            have arena->occupied[k] == old(arena->occupied[k]) by {
                instantiate(forall (j: int32) { end <= j and j < arena->capacity implies arena->occupied[j] == at(mark_free_run.entry, arena->occupied[j]) }, k) using {
                    end <= k;
                    k < arena->capacity;
                };
            }
            have 0 <= end by {
                arithmetic_certificate signed_int32 {
                    premise 0: (at(function.entry, 0) as int32) <= (at(function.entry, count) as
                        int32) => (at(function.entry, 0) as int32) <= (at(function.entry, count) as
                        int32);
                    premise 1: (count as int32) <= (end as int32) => (count as int32) <= (end as
                        int32);
                    add 0, 1 => (to_integer((at(function.entry, 0) as int32)) + to_integer((count as
                        int32))) <= (to_integer((at(function.entry, count) as int32)) +
                        to_integer((end as int32)));
                    conclusion 2;
                }
            }
            have 0 <= k by {
                arithmetic_certificate signed_int32 {
                    premise 0: (at(function.entry, 0) as int32) <= (at(function.entry, end) as
                        int32) => (at(function.entry, 0) as int32) <= (at(function.entry, end) as
                        int32);
                    premise 1: (end as int32) <= (k as int32) => (end as int32) <= (k as int32);
                    add 0, 1 => (to_integer((at(function.entry, 0) as int32)) + to_integer((end as
                        int32))) <= (to_integer((at(function.entry, end) as int32)) + to_integer((k
                        as int32)));
                    conclusion 2;
                }
            }
            instantiate(forall (j: int32) { at(mark_free_run.entry, 0) <= at(mark_free_run.entry, j) and at(mark_free_run.entry, j) < at(mark_free_run.entry, arena->capacity) implies at(mark_free_run.entry, arena->occupied[j]) == old(arena->occupied[j]) }, k) using {
                0 <= k;
                k < arena->capacity;
            };
            normalize() using {
                arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]);
                at(mark_free_run.entry, arena->occupied[k]) == old(arena->occupied[k]);
            };
        }
        mark marked;
        step();
        step();
        step();
        have arena->live_regions == n by {
            assumption();
        }
        have n < 2147483647 by {
            assumption();
        }
        have defined((n + 1)) by {
            extract(at(loop(0).exit, 0) <= at(loop(0).exit, run_length));
            extract(at(loop(0).exit, run_length) <= at(loop(0).exit, count));
            extract(at(function.entry, arena->capacity) <= at(function.entry, 1073741823));
            extract((let integer_value: Integer = to_integer((run_lo as int32)) + to_integer((count as int32)); integer_value) <= 2147483647);
            extract((let integer_value: Integer = (to_integer((end as int32)) - to_integer((count as int32))); integer_value) <= 2147483647);
            extract((let integer_value: Integer = to_integer((run_lo as int32)) + to_integer((count as int32)); integer_value) >= -2147483648);
            extract((let integer_value: Integer = (to_integer((end as int32)) - to_integer((count as int32))); integer_value) >= -2147483648);
            arithmetic_certificate rules {
                premise 0: at(function.entry, st.live) < at(function.entry, 2147483647) =>
                    at(function.entry, st.live) < at(function.entry, 2147483647);
                int32_defined bounds [0] => defined((n + 1));
                conclusion 0;
            }
        }
        step();
        have region->start == start by {
            normalize();
        }
        have region->end == end by {
            normalize();
        }
        have forall (k: int32) { region->start <= k and k < region->end implies arena->occupied[k] == 1 } by {
            intro();
            intro();
            extract(region->start <= k);
            extract(k < region->end);
            have start <= k by {
                assumption();
            }
            have k < end by {
                assumption();
            }
            have 0 <= k by {
                arithmetic_certificate signed_int32 {
                    premise 0: (at(function.entry, 0) as int32) < (at(function.entry, count) as
                        int32) => (at(function.entry, 0) as int32) < (at(function.entry, count) as
                        int32);
                    premise 1: (at(function.entry, start) as int32) < (at(function.entry, end) as
                        int32) => (at(function.entry, start) as int32) < (at(function.entry, end) as
                        int32);
                    premise 2: (count as int32) <= (end as int32) => (count as int32) <= (end as
                        int32);
                    premise 3: (at(function.entry, end) as int32) <= (at(function.entry,
                        arena->capacity) as int32) => (at(function.entry, end) as int32) <=
                        (at(function.entry, arena->capacity) as int32);
                    premise 4: (at(function.entry, arena->capacity) as int32) <= (at(function.entry,
                        536870911) as int32) => (at(function.entry, arena->capacity) as int32) <=
                        (at(function.entry, 536870911) as int32);
                    premise 5: (at(function.entry, start) as int32) <= (at(function.entry, end) as
                        int32) => (at(function.entry, start) as int32) <= (at(function.entry, end)
                        as int32);
                    premise 6: (at(function.entry, start) as int32) <= (at(function.entry, k) as
                        int32) => (at(function.entry, start) as int32) <= (at(function.entry, k) as
                        int32);
                    add 2, 0 => (to_integer((count as int32)) + to_integer((at(function.entry, 0) as
                        int32))) < (to_integer((end as int32)) + to_integer((at(function.entry,
                        count) as int32)));
                    add 3, 4 => (to_integer((at(function.entry, end) as int32)) +
                        to_integer((at(function.entry, arena->capacity) as int32))) <=
                        (to_integer((at(function.entry, arena->capacity) as int32)) +
                        to_integer((at(function.entry, 536870911) as int32)));
                    interval_from_affine 7 (end) (1) (2147483647);
                    interval_from_affine 8 (end) (-2147483648) (536870911);
                    interval_intersect 9, 10 (1) (536870911);
                    add 2, 8 => (to_integer((count as int32)) + (to_integer((at(function.entry, end)
                        as int32)) + to_integer((at(function.entry, arena->capacity) as int32)))) <=
                        (to_integer((end as int32)) + (to_integer((at(function.entry,
                        arena->capacity) as int32)) + to_integer((at(function.entry, 536870911) as
                        int32))));
                    interval_from_affine 0 (count) (1) (2147483647);
                    interval_from_affine 12 (count) (-2147483648) (536870911);
                    interval_intersect 13, 14 (1) (536870911);
                    interval_subtract 11, 15 11 (-536870910) (536870910);
                    affine_premise 6 16 16 => to_integer((at(function.entry, start) as int32)) <=
                        to_integer((at(function.entry, k) as int32));
                    add 2, 17 => 0 <= k;
                    conclusion 18;
                }
            }
            have k < arena->capacity by {
                arithmetic_certificate {
                    premise 0: at(function.entry, k) < at(function.entry, end) => at(function.entry,
                        k) < at(function.entry, end);
                    premise 1: at(function.entry, end) <= at(function.entry, arena->capacity) =>
                        at(function.entry, end) <= at(function.entry, arena->capacity);
                    add 0, 1 => (at(function.entry, to_integer((k as int32))) + at(function.entry,
                        to_integer((end as int32)))) < (at(function.entry, to_integer((end as
                        int32))) + at(function.entry, to_integer((arena->capacity as int32))));
                    conclusion 2;
                }
            }
            instantiate(forall (j: int32) { at(marked, start) <= at(marked, j) and at(marked, j) < at(marked, end) implies at(marked, arena->occupied[j]) == at(marked, 1) }, k) using {
                start <= k;
                k < end;
            };
            transport(at(marked, arena->occupied[k]) == at(marked, 1), arena->occupied[k] == 1) using {
                at(marked, arena->occupied[k]) == at(marked, 1);
                0 <= k;
                k < arena->capacity;
                separate(memory(*arena), memory(arena->occupied[0..arena->capacity]));
            };
        }
        have forall (k: int32) { 0 <= k and k < region->start implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            extract(0 <= k);
            extract(k < region->start);
            have k < start by {
                assumption();
            }
            have k < end by {
                arithmetic_certificate {
                    premise 0: at(function.entry, k) < at(function.entry, start) =>
                        at(function.entry, k) < at(function.entry, start);
                    premise 1: at(function.entry, start) < at(function.entry, end) =>
                        at(function.entry, start) < at(function.entry, end);
                    add 0, 1 => (at(function.entry, to_integer((k as int32))) + 1 +
                        (at(function.entry, to_integer((start as int32))) + 1)) <=
                        (at(function.entry, to_integer((start as int32))) + at(function.entry,
                        to_integer((end as int32))));
                    trivial => -1 <= 0;
                    add 2, 3 => (at(function.entry, to_integer((k as int32))) + 1 +
                        (at(function.entry, to_integer((start as int32))) + 1) + -1) <=
                        (at(function.entry, to_integer((start as int32))) + at(function.entry,
                        to_integer((end as int32))) + 0);
                    conclusion 4;
                }
            }
            have k < arena->capacity by {
                arithmetic_certificate {
                    premise 0: at(function.entry, k) < at(function.entry, end) => at(function.entry,
                        k) < at(function.entry, end);
                    premise 1: at(function.entry, end) <= at(function.entry, arena->capacity) =>
                        at(function.entry, end) <= at(function.entry, arena->capacity);
                    add 0, 1 => (at(function.entry, to_integer((k as int32))) + at(function.entry,
                        to_integer((end as int32)))) < (at(function.entry, to_integer((end as
                        int32))) + at(function.entry, to_integer((arena->capacity as int32))));
                    conclusion 2;
                }
            }
            instantiate(forall (j: int32) { at(marked, 0) <= at(marked, j) and at(marked, j) < at(marked, start) implies at(marked, arena->occupied[j]) == old(arena->occupied[j]) }, k) using {
                0 <= k;
                k < start;
            };
            transport(at(marked, arena->occupied[k]) == old(arena->occupied[k]), arena->occupied[k] == old(arena->occupied[k])) using {
                at(marked, arena->occupied[k]) == old(arena->occupied[k]);
                0 <= k;
                k < arena->capacity;
                separate(memory(*arena), memory(arena->occupied[0..arena->capacity]));
            };
        }
        have forall (k: int32) { region->end <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            extract(region->end <= k);
            extract(k < arena->capacity);
            have end <= k by {
                assumption();
            }
            have 0 <= end by {
                arithmetic_certificate signed_int32 {
                    premise 0: (at(function.entry, 0) as int32) <= (at(function.entry, count) as
                        int32) => (at(function.entry, 0) as int32) <= (at(function.entry, count) as
                        int32);
                    premise 1: (count as int32) <= (end as int32) => (count as int32) <= (end as
                        int32);
                    add 0, 1 => (to_integer((at(function.entry, 0) as int32)) + to_integer((count as
                        int32))) <= (to_integer((at(function.entry, count) as int32)) +
                        to_integer((end as int32)));
                    conclusion 2;
                }
            }
            have 0 <= k by {
                arithmetic_certificate signed_int32 {
                    premise 0: (at(function.entry, 0) as int32) <= (at(function.entry, end) as
                        int32) => (at(function.entry, 0) as int32) <= (at(function.entry, end) as
                        int32);
                    premise 1: (at(function.entry, end) as int32) <= (at(function.entry, k) as
                        int32) => (at(function.entry, end) as int32) <= (at(function.entry, k) as
                        int32);
                    add 0, 1 => (to_integer((at(function.entry, 0) as int32)) +
                        to_integer((at(function.entry, end) as int32))) <=
                        (to_integer((at(function.entry, end) as int32)) +
                        to_integer((at(function.entry, k) as int32)));
                    conclusion 2;
                }
            }
            instantiate(forall (j: int32) { at(marked, end) <= at(marked, j) and at(marked, j) < at(marked, arena->capacity) implies at(marked, arena->occupied[j]) == old(arena->occupied[j]) }, k) using {
                end <= k;
                k < arena->capacity;
            };
            transport(at(marked, arena->occupied[k]) == old(arena->occupied[k]), arena->occupied[k] == old(arena->occupied[k])) using {
                at(marked, arena->occupied[k]) == old(arena->occupied[k]);
                0 <= k;
                k < arena->capacity;
                separate(memory(*arena), memory(arena->occupied[0..arena->capacity]));
            };
        }
        mark stored;
        have forall (k: int32) { region->start <= k and k < region->end implies old(arena->occupied[k]) == 0 } by {
            intro();
            intro();
            extract(region->start <= k);
            extract(k < region->end);
            have start <= k by {
                assumption();
            }
            have k < end by {
                assumption();
            }
            instantiate(forall (j: int32) { start <= j and j < end implies old(arena->occupied[j]) == 0 }, k) using {
                start <= k;
                k < end;
            };
        }
        fold(arena_cells(arena->data, arena->occupied, arena->capacity));
        let allocated = fold(arena_region(region), { start: start, end: end });
        let st = fold(arena_state(arena), { live: (n + 1), capacity: arena->capacity });
        let outcome = fold(arena_alloc_result(region), { model: ArenaAllocOutcome::Success(start, end) });
        step();
        have result == 1 by {
            normalize();
        }
        have forall (k: int32) { result == 0 and 0 <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            extract(result == 0);
            have not result == 0 by {
                normalize();
            }
            contradiction(result == 0);
        }
        assumption();
        have result == 0 or result == 1 by {
            assumption();
        }
        assumption();
        have to_integer(st.live) == (to_integer(old(st.live)) + to_integer(result)) by {
            have -2147483648 <= (to_integer(old(st.live)) + 1) by {
                assumption();
            }
            have (to_integer(old(st.live)) + 1) <= 2147483647 by {
                assumption();
            }
            have to_integer(st.live) == (to_integer(old(st.live)) + 1) by {
                arithmetic_certificate rules {
                    premise 0: -2147483648 <= (to_integer(old(st.live)) + 1) => -2147483648 <=
                        (to_integer(old(st.live)) + 1);
                    premise 1: (to_integer(old(st.live)) + 1) <= 2147483647 =>
                        (to_integer(old(st.live)) + 1) <= 2147483647;
                    integer_operation_identity bounds [0, 1] => to_integer(st.live) ==
                        (to_integer(old(st.live)) + 1);
                    conclusion 0;
                }
            }
            assumption();
        }
        assumption();
        have arena->capacity == old(arena->capacity) by {
            normalize();
        }
        assumption();
        have arena->capacity <= 536870911 by {
            assumption();
        }
        assumption();
        have st.capacity == arena->capacity by {
            normalize();
        }
        assumption();
        have result == 0 implies outcome.model == ArenaAllocOutcome::Failure() by {
            intro();
            contradiction(result == 0);
        }
        assumption();
        have result == 1 implies outcome.model == ArenaAllocOutcome::Success(region->start, region->end) by {
            intro();
            normalize();
        }
        assumption();
        have result == 1 implies region->arena == arena by {
            intro();
            assumption();
        }
        assumption();
        have result == 1 implies to_integer(region->end) == (to_integer(region->start) + to_integer(count)) by {
            intro();
            assumption();
        }
        assumption();
        have result == 1 implies region->end <= arena->capacity by {
            intro();
            assumption();
        }
        assumption();
        have result == 1 implies 0 <= region->start by {
            intro();
            assumption();
        }
        assumption();
        have result == 1 implies region->start < region->end by {
            intro();
            assumption();
        }
        assumption();
        have forall (k: int32) { result == 1 and region->start <= k and k < region->end implies arena->occupied[k] == 1 } by {
            intro();
            intro();
            extract(region->start <= k);
            extract(k < region->end);
            have arena->occupied[k] == 1 by {
                instantiate(forall (j: int32) { at(stored, region->start) <= at(stored, j) and at(stored, j) < at(stored, region->end) implies at(stored, arena->occupied[j]) == at(stored, 1) }, k) using {
                    region->start <= k;
                    k < region->end;
                };
            }
            transport(at(stored, arena->occupied[k]) == at(stored, 1), arena->occupied[k] == 1) using {
                at(stored, arena->occupied[k]) == at(stored, 1);
            };
        }
        assumption();
        have forall (k: int32) { result == 1 and 0 <= k and k < region->start implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            extract(0 <= k);
            extract(k < region->start);
            have arena->occupied[k] == old(arena->occupied[k]) by {
                instantiate(forall (j: int32) { at(stored, 0) <= at(stored, j) and at(stored, j) < at(stored, region->start) implies at(stored, arena->occupied[j]) == old(arena->occupied[j]) }, k) using {
                    0 <= k;
                    k < region->start;
                };
            }
            transport(at(stored, arena->occupied[k]) == old(arena->occupied[k]), arena->occupied[k] == old(arena->occupied[k])) using {
                at(stored, arena->occupied[k]) == old(arena->occupied[k]);
            };
        }
        assumption();
        have forall (k: int32) { result == 1 and region->end <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k]) } by {
            intro();
            intro();
            extract(region->end <= k);
            extract(k < arena->capacity);
            have arena->occupied[k] == old(arena->occupied[k]) by {
                instantiate(forall (j: int32) { at(stored, region->end) <= at(stored, j) and at(stored, j) < at(stored, arena->capacity) implies at(stored, arena->occupied[j]) == old(arena->occupied[j]) }, k) using {
                    region->end <= k;
                    k < arena->capacity;
                };
            }
            transport(at(stored, arena->occupied[k]) == old(arena->occupied[k]), arena->occupied[k] == old(arena->occupied[k])) using {
                at(stored, arena->occupied[k]) == old(arena->occupied[k]);
            };
        }
        assumption();
        have forall (k: int32) { result == 1 and region->start <= k and k < region->end implies old(arena->occupied[k]) == 0 } by {
            intro();
            intro();
            extract(region->start <= k);
            extract(k < region->end);
            instantiate(forall (j: int32) { at(stored, region->start) <= at(stored, j) and at(stored, j) < at(stored, region->end) implies old(arena->occupied[j]) == 0 }, k) using {
                region->start <= k;
                k < region->end;
            };
        }
        assumption();
        assumption();
        assumption();
    }
}

verifying "arena_free.c";

void arena_free(struct region* region) {
    consumes r: arena_region(region);
    consumes st: arena_state(region->arena);
    requires 1 <= st.live;
    requires r.end <= st.capacity;
    produces *region;
    produces after: arena_state(region->arena);

    ensures region->arena == old(region->arena);
    ensures region->start == old(r.start);
    ensures region->end == old(r.end);
    ensures after.live == old(st.live) - 1;
    ensures after.capacity == old(st.capacity);
    ensures region->arena->capacity == old(region->arena->capacity);
    ensures forall (k: int32) {
        region->start <= k and k < region->end implies region->arena->occupied[k] == 0
    };
    ensures forall (k: int32) {
        0 <= k and k < region->start implies
            region->arena->occupied[k] == old(region->arena->occupied[k])
    };
    ensures forall (k: int32) {
        region->end <= k and k < region->arena->capacity implies
            region->arena->occupied[k] == old(region->arena->occupied[k])
    };
} by {
    let { live: n, capacity: c } = unfold(st);
    let { start: s, end: e } = unfold(r);
    unfold(arena_cells(region->arena->data, region->arena->occupied, region->arena->capacity));
    have viewable(region->arena->occupied[0..region->arena->capacity]) by {
        assumption();
    }
    have separate(memory(*region), memory(region->arena->occupied[0..region->arena->capacity])) by {
        assumption();
    }
    mark unfolded;
    step();
    have separate(statement(0).footprint, memory(region->arena)) by {
        normalize() using {};
    }
    have region->arena == at(statement(0).entry, region->arena) by {
        transport_certificate {
            premise 0: separate(statement(0).footprint, memory(region->arena)) => separate(statement(0).footprint, memory(region->arena));
            preserve 0 => region->arena == at(statement(0).entry, region->arena);
            conclusion 1;
        }
    }
    have separate(statement(0).footprint, memory(region->arena->data)) by {
        normalize() using {};
    }
    have region->arena->data == at(statement(0).entry, region->arena->data) by {
        transport_certificate {
            premise 0: separate(statement(0).footprint, memory(region->arena->data)) => separate(statement(0).footprint, memory(region->arena->data));
            preserve 0 => region->arena->data == at(statement(0).entry, region->arena->data);
            conclusion 1;
        }
    }
    have separate(statement(0).footprint, memory(region->arena->occupied)) by {
        normalize() using {};
    }
    have region->arena->occupied == at(statement(0).entry, region->arena->occupied) by {
        transport_certificate {
            premise 0: separate(statement(0).footprint, memory(region->arena->occupied)) => separate(statement(0).footprint, memory(region->arena->occupied));
            preserve 0 => region->arena->occupied == at(statement(0).entry, region->arena->occupied);
            conclusion 1;
        }
    }
    step();
    have separate(statement(1).footprint, memory(region->arena)) by {
        normalize() using {};
    }
    have region->arena == at(statement(1).entry, region->arena) by {
        transport_certificate {
            premise 0: separate(statement(1).footprint, memory(region->arena)) => separate(statement(1).footprint, memory(region->arena));
            preserve 0 => region->arena == at(statement(1).entry, region->arena);
            conclusion 1;
        }
    }
    have separate(statement(1).footprint, memory(region->arena->data)) by {
        normalize() using {};
    }
    have region->arena->data == at(statement(1).entry, region->arena->data) by {
        transport_certificate {
            premise 0: separate(statement(1).footprint, memory(region->arena->data)) => separate(statement(1).footprint, memory(region->arena->data));
            preserve 0 => region->arena->data == at(statement(1).entry, region->arena->data);
            conclusion 1;
        }
    }
    have separate(statement(1).footprint, memory(region->arena->occupied)) by {
        normalize() using {};
    }
    have region->arena->occupied == at(statement(1).entry, region->arena->occupied) by {
        transport_certificate {
            premise 0: separate(statement(1).footprint, memory(region->arena->occupied)) => separate(statement(1).footprint, memory(region->arena->occupied));
            preserve 0 => region->arena->occupied == at(statement(1).entry, region->arena->occupied);
            conclusion 1;
        }
    }
    step();
    have separate(statement(2).footprint, memory(region->arena)) by {
        normalize() using {};
    }
    have region->arena == at(statement(2).entry, region->arena) by {
        transport_certificate {
            premise 0: separate(statement(2).footprint, memory(region->arena)) => separate(statement(2).footprint, memory(region->arena));
            preserve 0 => region->arena == at(statement(2).entry, region->arena);
            conclusion 1;
        }
    }
    have separate(statement(2).footprint, memory(region->arena->data)) by {
        normalize() using {};
    }
    have region->arena->data == at(statement(2).entry, region->arena->data) by {
        transport_certificate {
            premise 0: separate(statement(2).footprint, memory(region->arena->data)) => separate(statement(2).footprint, memory(region->arena->data));
            preserve 0 => region->arena->data == at(statement(2).entry, region->arena->data);
            conclusion 1;
        }
    }
    have separate(statement(2).footprint, memory(region->arena->occupied)) by {
        normalize() using {};
    }
    have region->arena->occupied == at(statement(2).entry, region->arena->occupied) by {
        transport_certificate {
            premise 0: separate(statement(2).footprint, memory(region->arena->occupied)) => separate(statement(2).footprint, memory(region->arena->occupied));
            preserve 0 => region->arena->occupied == at(statement(2).entry, region->arena->occupied);
            conclusion 1;
        }
    }
    step();
    have separate(statement(3).footprint, memory(region->arena)) by {
        normalize() using {};
    }
    have region->arena == at(statement(3).entry, region->arena) by {
        transport_certificate {
            premise 0: separate(statement(3).footprint, memory(region->arena)) => separate(statement(3).footprint, memory(region->arena));
            preserve 0 => region->arena == at(statement(3).entry, region->arena);
            conclusion 1;
        }
    }
    have separate(statement(3).footprint, memory(region->arena->data)) by {
        normalize() using {};
    }
    have region->arena->data == at(statement(3).entry, region->arena->data) by {
        transport_certificate {
            premise 0: separate(statement(3).footprint, memory(region->arena->data)) => separate(statement(3).footprint, memory(region->arena->data));
            preserve 0 => region->arena->data == at(statement(3).entry, region->arena->data);
            conclusion 1;
        }
    }
    have separate(statement(3).footprint, memory(region->arena->occupied)) by {
        normalize() using {};
    }
    have region->arena->occupied == at(statement(3).entry, region->arena->occupied) by {
        transport_certificate {
            premise 0: separate(statement(3).footprint, memory(region->arena->occupied)) => separate(statement(3).footprint, memory(region->arena->occupied));
            preserve 0 => region->arena->occupied == at(statement(3).entry, region->arena->occupied);
            conclusion 1;
        }
    }
    have arena == region->arena by {
        assumption();
    }
    have e <= c by {
        assumption();
    }
    have arena->capacity == c by {
        assumption();
    }
    have e <= arena->capacity by {
        assumption();
    }
    have forall (k: int32) { region->start <= k and k < region->start implies arena->occupied[k] == 0 } by {
        intro();
        intro();
        extract(region->start <= k);
        extract(k < region->start);
        have not k < region->start by {
            assumption();
        }
        contradiction(k < region->start);
    }
    have viewable(arena->occupied[0..arena->capacity]) by {
        transport(at(unfolded, viewable(region->arena->occupied[0..region->arena->capacity])), viewable(arena->occupied[0..arena->capacity])) using {
            at(unfolded, viewable(region->arena->occupied[0..region->arena->capacity]));
        };
    }
    have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == old(region->arena->occupied[k]) } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        transport(old(region->arena->occupied[k]) == old(region->arena->occupied[k]), arena->occupied[k] == old(region->arena->occupied[k])) using {
            0 <= k;
            k < arena->capacity;
        };
    }
    let w = fold(arena_clear_window(arena->data, arena->occupied, arena->capacity, region->start, region->end), { next: region->start });
    loop as clear_occupied {
        decreases (to_integer(region->end) - to_integer(i));
        owns w: arena_clear_window(arena->data, arena->occupied, arena->capacity, region->start, region->end);
        invariant w.next == i;
        invariant forall (k: int32) { 0 <= k and k < region->start implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) };
        invariant forall (k: int32) { region->end <= k and k < arena->capacity implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) };
        invariant arena->data == at(clear_occupied.entry, arena->data);
        invariant arena->occupied == at(clear_occupied.entry, arena->occupied);
        invariant region->arena == old(region->arena);
        initialize by {
            have w.next == i by {
                normalize();
            }
            have forall (k: int32) { 0 <= k and k < region->start implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } by {
                intro();
                intro();
                normalize();
            }
            have forall (k: int32) { region->end <= k and k < arena->capacity implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } by {
                intro();
                intro();
                normalize();
            }
            have arena->data == at(clear_occupied.entry, arena->data) by {
                normalize();
            }
            have arena->occupied == at(clear_occupied.entry, arena->occupied) by {
                normalize();
            }
            have region->arena == old(region->arena) by {
                normalize();
            }
        }
        preserve by {
            let { next: m } = unfold(w);
            have m == i by {
                assumption();
            }
            have 0 <= region->start by {
                assumption();
            }
            have region->start <= m by {
                assumption();
            }
            have region->start <= i by {
                assumption();
            }
            have 0 <= i by {
                arithmetic_certificate {
                    premise 0: at(function.entry, 0) <= at(function.entry, region->start) =>
                        at(function.entry, 0) <= at(function.entry, region->start);
                    premise 1: at(function.entry, region->start) <= at(function.entry, i) =>
                        at(function.entry, region->start) <= at(function.entry, i);
                    add 0, 1 => (at(function.entry, 0) + at(function.entry,
                        to_integer((region->start as int32)))) <= (at(function.entry,
                        to_integer((region->start as int32))) + at(function.entry, to_integer((i as
                        int32))));
                    conclusion 2;
                }
            }
            have region->end <= arena->capacity by {
                assumption();
            }
            have i < arena->capacity by {
                arithmetic_certificate {
                    premise 0: at(region(5).entry, i) < at(region(5).entry, region->end) =>
                        at(region(5).entry, i) < at(region(5).entry, region->end);
                    premise 1: at(function.entry, region->end) <= at(function.entry,
                        arena->capacity) => at(function.entry, region->end) <= at(function.entry,
                        arena->capacity);
                    add 0, 1 => (at(region(5).entry, to_integer((i as int32))) + at(function.entry,
                        to_integer((region->end as int32)))) < (at(region(5).entry,
                        to_integer((region->end as int32))) + at(function.entry,
                        to_integer((arena->capacity as int32))));
                    conclusion 2;
                }
            }
            mark opened;
            have contains(memory(*arena), memory(arena->occupied)) by {
                normalize();
            }
            have separate(memory(arena->occupied), memory(arena->occupied[i])) by {
                apply(selected_array_cell(memory(*arena), memory(arena->occupied), arena->occupied, arena->capacity, i)) using {
                    separate(memory(*arena), memory(arena->occupied[0..arena->capacity]));
                    contains(memory(*arena), memory(arena->occupied));
                    0 <= i;
                    i < arena->capacity;
                };
            }
            have separate(memory(arena->occupied), memory(at(clear_occupied.entry, arena->occupied)[i])) by {
                rewrite(at(clear_occupied.entry, arena->occupied) == arena->occupied);
                assumption();
            }
            have contains(memory(*arena), memory(arena->data)) by {
                normalize();
            }
            have separate(memory(arena->data), memory(arena->occupied[i])) by {
                apply(selected_array_cell(memory(*arena), memory(arena->data), arena->occupied, arena->capacity, i)) using {
                    separate(memory(*arena), memory(arena->occupied[0..arena->capacity]));
                    contains(memory(*arena), memory(arena->data));
                    0 <= i;
                    i < arena->capacity;
                };
            }
            have separate(memory(arena->data), memory(at(clear_occupied.entry, arena->occupied)[i])) by {
                rewrite(at(clear_occupied.entry, arena->occupied) == arena->occupied);
                assumption();
            }
            have contains(memory(*region), memory(region->arena)) by {
                normalize();
            }
            have separate(memory(region->arena), memory(arena->occupied[i])) by {
                apply(selected_array_cell(memory(*region), memory(region->arena), arena->occupied, arena->capacity, i)) using {
                    separate(memory(*region), memory(arena->occupied[0..arena->capacity]));
                    contains(memory(*region), memory(region->arena));
                    0 <= i;
                    i < arena->capacity;
                };
            }
            have separate(memory(region->arena), memory(at(clear_occupied.entry, arena->occupied)[i])) by {
                rewrite(at(clear_occupied.entry, arena->occupied) == arena->occupied);
                assumption();
            }
            step();
            transport(at(opened, region->start) == at(opened, region->start), region->start == at(opened, region->start)) using {
                at(opened, separate(memory(*region), memory(arena->occupied[0..arena->capacity])));
                0 <= at(opened, i);
                at(opened, i) < at(opened, arena->capacity);
            };
            transport(at(opened, region->end) == at(opened, region->end), region->end == at(opened, region->end)) using {
                at(opened, separate(memory(*region), memory(arena->occupied[0..arena->capacity])));
                0 <= at(opened, i);
                at(opened, i) < at(opened, arena->capacity);
            };
            have separate(statement(4).statement(0).footprint, memory(arena->occupied)) by {
                normalize() using {
                    separate(memory(arena->occupied), memory(at(clear_occupied.entry,
                        arena->occupied)[i]));
                };
            }
            have arena->occupied == at(opened, arena->occupied) by {
                transport_certificate {
                    premise 0: separate(statement(4).statement(0).footprint, memory(arena->occupied)) => separate(statement(4).statement(0).footprint, memory(arena->occupied));
                    preserve 0 => arena->occupied == at(opened, arena->occupied);
                    conclusion 1;
                }
            }
            have separate(statement(4).statement(0).footprint, memory(arena->data)) by {
                normalize() using {
                    separate(memory(arena->data), memory(at(clear_occupied.entry,
                        arena->occupied)[i]));
                };
            }
            have arena->data == at(opened, arena->data) by {
                transport_certificate {
                    premise 0: separate(statement(4).statement(0).footprint, memory(arena->data)) => separate(statement(4).statement(0).footprint, memory(arena->data));
                    preserve 0 => arena->data == at(opened, arena->data);
                    conclusion 1;
                }
            }
            transport(at(opened, arena->capacity) == at(opened, arena->capacity), arena->capacity == at(opened, arena->capacity)) using {
                at(opened, separate(memory(*arena), memory(arena->occupied[0..arena->capacity])));
                at(opened, separate(memory(*arena), memory(arena->data[0..arena->capacity])));
                0 <= at(opened, i);
                at(opened, i) < at(opened, arena->capacity);
            };
            have separate(statement(4).statement(0).footprint, memory(region->arena)) by {
                normalize() using {
                    separate(memory(region->arena), memory(at(clear_occupied.entry,
                        arena->occupied)[i]));
                };
            }
            have region->arena == at(opened, region->arena) by {
                transport_certificate {
                    premise 0: separate(statement(4).statement(0).footprint, memory(region->arena)) => separate(statement(4).statement(0).footprint, memory(region->arena));
                    preserve 0 => region->arena == at(opened, region->arena);
                    conclusion 1;
                }
            }
            mark cleared;
            give(at(opened, arena->data)[i..(i + 1)]);
            step();
            have to_integer(region->start) <= (to_integer(at(opened, i)) + 1) by {
                arithmetic_certificate {
                    negated_goal => (to_integer(at(opened, i)) + 1) < to_integer(region->start);
                    premise 0: to_integer(old(region->start)) <= to_integer(at(opened, i)) =>
                        to_integer(old(region->start)) <= to_integer(at(opened, i));
                    premise 1: to_integer(region->start) == to_integer(old(region->start)) =>
                        to_integer(region->start) == to_integer(old(region->start));
                    less_equal_from_equal 2 => to_integer(region->start) <=
                        to_integer(old(region->start));
                    add 0, 1 => (to_integer(at(opened, i)) + 1 + to_integer(old(region->start))) <
                        (to_integer(region->start) + to_integer(at(opened, i)));
                    add 4, 3 => (to_integer(at(opened, i)) + 1 + to_integer(old(region->start)) +
                        to_integer(region->start)) < (to_integer(region->start) +
                        to_integer(at(opened, i)) + to_integer(old(region->start)));
                    conclusion 5;
                }
            }
            have forall (k: int32) { region->start <= k and to_integer(k) < (to_integer(at(opened, i)) + 1) implies arena->occupied[k] == 0 } by {
                intro();
                intro();
                extract(region->start <= k);
                extract(to_integer(k) < (to_integer(at(opened, i)) + 1));
                if k < at(opened, i) {
                    have k < m by {
                        assumption();
                    }
                    have at(opened, arena->occupied[k]) == 0 by {
                        instantiate(forall (j: int32) { at(opened, region->start) <= at(opened, j) and at(opened, j) < at(opened, m) implies at(opened, arena->occupied[j]) == at(opened, 0) }, k) using {
                            region->start <= k;
                            region->start == at(opened, region->start);
                            k < m;
                        };
                    }
                    have 0 <= k by {
                        arithmetic_certificate signed_int32 {
                            premise 0: (at(function.entry, 0) as int32) <= (at(function.entry,
                                region->start) as int32) => (at(function.entry, 0) as int32) <=
                                (at(function.entry, region->start) as int32);
                            premise 1: (region->start as int32) <= (k as int32) => (region->start as
                                int32) <= (k as int32);
                            premise 2: (region->start as int32) == (at(opened, region->start) as
                                int32) => (region->start as int32) == (at(opened, region->start) as
                                int32);
                            interval_atom (0) (0) (0);
                            less_equal_from_equal 2 reverse => to_integer((at(opened, region->start)
                                as int32)) <= to_integer((region->start as int32));
                            add 4, 0 => (to_integer((at(opened, region->start) as int32)) +
                                to_integer((at(function.entry, 0) as int32))) <=
                                (to_integer((region->start as int32)) +
                                to_integer((at(function.entry, region->start) as int32)));
                            add 1, 5 => (to_integer((region->start as int32)) +
                                (to_integer((at(opened, region->start) as int32)) +
                                to_integer((at(function.entry, 0) as int32)))) <= (to_integer((k as
                                int32)) + (to_integer((region->start as int32)) +
                                to_integer((at(function.entry, region->start) as int32))));
                            interval_from_affine 6 (k) (0) (2147483647);
                            interval_compare 3, 7 le => 0 <= k;
                            conclusion 8;
                        }
                    }
                    have k < at(opened, arena->capacity) by {
                        arithmetic_certificate {
                            premise 0: at(region(5).entry, i) < at(region(5).entry, region->end) =>
                                at(region(5).entry, i) < at(region(5).entry, region->end);
                            premise 1: at(function.entry, region->end) <= at(function.entry,
                                arena->capacity) => at(function.entry, region->end) <=
                                at(function.entry, arena->capacity);
                            add 0, 1 => (at(region(5).entry, to_integer((i as int32))) +
                                at(function.entry, to_integer((region->end as int32)))) <
                                (at(region(5).entry, to_integer((region->end as int32))) +
                                at(function.entry, to_integer((arena->capacity as int32))));
                            trivial => -1 <= 0;
                            add 2, 3 => (at(region(5).entry, to_integer((i as int32))) +
                                at(function.entry, to_integer((region->end as int32))) + -1) <
                                (at(region(5).entry, to_integer((region->end as int32))) +
                                at(function.entry, to_integer((arena->capacity as int32))) + 0);
                            premise 2: k < at(region(5).entry, i) => k < at(region(5).entry, i);
                            add 4, 5 => (at(region(5).entry, to_integer((i as int32))) +
                                at(function.entry, to_integer((region->end as int32))) + -1 + 1 +
                                (to_integer((k as int32)) + 1)) <= (at(region(5).entry,
                                to_integer((region->end as int32))) + at(function.entry,
                                to_integer((arena->capacity as int32))) + 0 + at(region(5).entry,
                                to_integer((i as int32))));
                            conclusion 6;
                        }
                    }
                    transport(at(opened, arena->occupied[k]) == 0, at(opened, arena->occupied)[k] == 0) using {
                        at(opened, arena->occupied[k]) == 0;
                        arena->occupied == at(opened, arena->occupied);
                        arena->capacity == at(opened, arena->capacity);
                        at(opened, separate(memory(*arena),
                            memory(arena->occupied[0..arena->capacity])));
                        at(opened, separate(memory(*arena),
                            memory(arena->data[0..arena->capacity])));
                        k < at(opened, arena->capacity);
                        k < at(opened, i);
                        0 <= k;
                        0 <= at(opened, i);
                        at(opened, i) < arena->capacity;
                    };
                    rewrite(arena->occupied == at(opened, arena->occupied));
                    assumption();
                } else {
                    have to_integer(k) == to_integer(at(opened, i)) by {
                        arithmetic_certificate {
                            premise 0: to_integer(k) < (to_integer(at(opened, i)) + 1) =>
                                to_integer(k) < (to_integer(at(opened, i)) + 1);
                            premise 1: not k < at(opened, i) => not k < at(opened, i);
                            equal_from_bounds 0, 1 => to_integer(k) == to_integer(at(opened, i));
                            conclusion 2;
                        }
                    }
                    rewrite(k == at(opened, i));
                    rewrite(arena->occupied == at(opened, arena->occupied));
                    normalize();
                }
            }
            have forall (k: int32) { 0 <= k and k < region->start implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } by {
                intro();
                intro();
                extract(0 <= k);
                extract(k < region->start);
                have at(opened, arena->occupied[k]) == at(clear_occupied.entry, arena->occupied[k]) by {
                    instantiate(forall (j: int32) { at(opened, 0) <= at(opened, j) and at(opened, j) < at(opened, region->start) implies at(opened, arena->occupied[j]) == at(clear_occupied.entry, arena->occupied[j]) }, k) using {
                        0 <= k;
                        k < region->start;
                        region->start == at(opened, region->start);
                    };
                }
                have k < at(opened, i) by {
                    arithmetic_certificate {
                        premise 0: at(region(3).exit, i) <= at(region(5).entry, i) =>
                            at(region(3).exit, i) <= at(region(5).entry, i);
                        premise 1: region->start == at(opened, region->start) => region->start ==
                            at(opened, region->start);
                        less_equal_from_equal 1 => to_integer((region->start as int32)) <=
                            at(opened, to_integer((region->start as int32)));
                        add 0, 2 => (at(region(3).exit, to_integer((i as int32))) +
                            to_integer((region->start as int32))) <= (at(region(5).entry,
                            to_integer((i as int32))) + at(opened, to_integer((region->start as
                            int32))));
                        premise 2: k < region->start => k < region->start;
                        add 3, 4 => (at(region(3).exit, to_integer((i as int32))) +
                            to_integer((region->start as int32)) + to_integer((k as int32))) <
                            (at(region(5).entry, to_integer((i as int32))) + at(opened,
                            to_integer((region->start as int32))) + to_integer((region->start as
                            int32)));
                        conclusion 5;
                    }
                }
                transport(at(opened, arena->occupied[k]) == at(clear_occupied.entry, arena->occupied[k]), at(opened, arena->occupied)[k] == at(clear_occupied.entry, arena->occupied[k])) using {
                    at(opened, arena->occupied[k]) == at(clear_occupied.entry, arena->occupied[k]);
                    k < at(opened, i);
                    0 <= k;
                    0 <= at(opened, i);
                    at(opened, i) < arena->capacity;
                };
                rewrite(arena->occupied == at(opened, arena->occupied));
                assumption();
            }
            have forall (k: int32) { region->end <= k and k < arena->capacity implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } by {
                intro();
                intro();
                extract(region->end <= k);
                extract(k < arena->capacity);
                have at(opened, arena->occupied[k]) == at(clear_occupied.entry, arena->occupied[k]) by {
                    instantiate(forall (j: int32) { at(opened, region->end) <= at(opened, j) and at(opened, j) < at(opened, arena->capacity) implies at(opened, arena->occupied[j]) == at(clear_occupied.entry, arena->occupied[j]) }, k) using {
                        region->end <= k;
                        region->end == at(opened, region->end);
                        k < arena->capacity;
                        arena->capacity == at(opened, arena->capacity);
                    };
                }
                have at(opened, i) < k by {
                    arithmetic_certificate {
                        premise 0: region->end <= k => region->end <= k;
                        premise 1: region->end == at(opened, region->end) => region->end ==
                            at(opened, region->end);
                        less_equal_from_equal 1 reverse => at(opened, to_integer((region->end as
                            int32))) <= to_integer((region->end as int32));
                        add 0, 2 => (to_integer((region->end as int32)) + at(opened,
                            to_integer((region->end as int32)))) <= (to_integer((k as int32)) +
                            to_integer((region->end as int32)));
                        premise 2: at(region(5).entry, i) < at(region(5).entry, region->end) =>
                            at(region(5).entry, i) < at(region(5).entry, region->end);
                        add 3, 4 => (to_integer((region->end as int32)) + at(opened,
                            to_integer((region->end as int32))) + at(region(5).entry, to_integer((i
                            as int32)))) < (to_integer((k as int32)) + to_integer((region->end as
                            int32)) + at(region(5).entry, to_integer((region->end as int32))));
                        conclusion 5;
                    }
                }
                have at(opened, i) <= k by {
                    arithmetic_certificate {
                        premise 0: at(opened, i) < k => at(opened, i) < k;
                        trivial => -1 <= 0;
                        add 0, 1 => (at(opened, to_integer((i as int32))) + -1) < (to_integer((k as
                            int32)) + 0);
                        conclusion 2;
                    }
                }
                have 0 <= k by {
                    arithmetic_certificate signed_int32 {
                        premise 0: (0 as int32) <= (at(region(5).entry, i) as int32) => (0 as int32)
                            <= (at(region(5).entry, i) as int32);
                        premise 1: (at(opened, i) as int32) <= (k as int32) => (at(opened, i) as
                            int32) <= (k as int32);
                        add 0, 1 => (to_integer((0 as int32)) + to_integer((at(opened, i) as
                            int32))) <= (to_integer((at(region(5).entry, i) as int32)) +
                            to_integer((k as int32)));
                        conclusion 2;
                    }
                }
                transport(at(opened, arena->occupied[k]) == at(clear_occupied.entry, arena->occupied[k]), at(opened, arena->occupied)[k] == at(clear_occupied.entry, arena->occupied[k])) using {
                    at(opened, arena->occupied[k]) == at(clear_occupied.entry, arena->occupied[k]);
                    at(opened, i) < k;
                    0 <= at(opened, i);
                    at(opened, i) < arena->capacity;
                    0 <= k;
                    k < arena->capacity;
                };
                rewrite(arena->occupied == at(opened, arena->occupied));
                assumption();
            }
            have forall (k: int32) { region->start <= k and k < i implies arena->occupied[k] == 0 } by {
                intro();
                intro();
                extract(region->start <= k);
                extract(k < i);
                have to_integer(k) < (to_integer(at(opened, i)) + 1) by {
                    have -2147483648 <= (to_integer(at(opened, i)) + 1) by {
                        arithmetic_certificate {
                            negated_goal => (to_integer(at(opened, i)) + 1) < -2147483648;
                            premise 0: 0 <= to_integer(at(opened, i)) => 0 <= to_integer(at(opened,
                                i));
                            add 0, 1 => (to_integer(at(opened, i)) + 1 + 0) < (-2147483648 +
                                to_integer(at(opened, i)));
                            conclusion 2;
                        }
                    }
                    have (to_integer(at(opened, i)) + 1) <= 2147483647 by {
                        arithmetic_certificate {
                            negated_goal => 2147483647 < (to_integer(at(opened, i)) + 1);
                            premise 0: to_integer(at(opened, i)) < to_integer(at(region(5).entry,
                                arena->capacity)) => to_integer(at(opened, i)) <
                                to_integer(at(region(5).entry, arena->capacity));
                            premise 1: to_integer(at(region(5).entry, arena->capacity)) <= 536870911
                                => to_integer(at(region(5).entry, arena->capacity)) <= 536870911;
                            add 0, 1 => (2147483647 + 1 + (to_integer(at(opened, i)) + 1)) <=
                                (to_integer(at(opened, i)) + 1 + to_integer(at(region(5).entry,
                                arena->capacity)));
                            add 3, 2 => (2147483647 + 1 + (to_integer(at(opened, i)) + 1) +
                                to_integer(at(region(5).entry, arena->capacity))) <=
                                (to_integer(at(opened, i)) + 1 + to_integer(at(region(5).entry,
                                arena->capacity)) + 536870911);
                            conclusion 4;
                        }
                    }
                    have to_integer((i as int32)) == (to_integer(at(opened, i)) + 1) by {
                        arithmetic_certificate rules {
                            premise 0: -2147483648 <= (to_integer(at(opened, i)) + 1) => -2147483648
                                <= (to_integer(at(opened, i)) + 1);
                            premise 1: (to_integer(at(opened, i)) + 1) <= 2147483647 =>
                                (to_integer(at(opened, i)) + 1) <= 2147483647;
                            integer_operation_identity bounds [0, 1] => to_integer((i as int32)) ==
                                (to_integer(at(opened, i)) + 1);
                            conclusion 0;
                        }
                    }
                    arithmetic_certificate {
                        negated_goal => (to_integer(at(opened, i)) + 1) <= to_integer(k);
                        premise 0: to_integer((i as int32)) == (to_integer(at(opened, i)) + 1) =>
                            to_integer((i as int32)) == (to_integer(at(opened, i)) + 1);
                        less_equal_from_equal 1 => to_integer((i as int32)) <=
                            (to_integer(at(opened, i)) + 1);
                        premise 1: to_integer(k) < to_integer((i as int32)) => to_integer(k) <
                            to_integer((i as int32));
                        add 0, 2 => (to_integer(at(opened, i)) + 1 + to_integer((i as int32))) <=
                            (to_integer(k) + (to_integer(at(opened, i)) + 1));
                        add 4, 3 => (to_integer(at(opened, i)) + 1 + to_integer((i as int32)) +
                            to_integer(k)) < (to_integer(k) + (to_integer(at(opened, i)) + 1) +
                            to_integer((i as int32)));
                        conclusion 5;
                    }
                }
                instantiate(forall (j: int32) { region->start <= j and to_integer(j) < (to_integer(at(opened, i)) + 1) implies arena->occupied[j] == 0 }, k) using {
                    region->start <= k;
                    to_integer(k) < (to_integer(at(opened, i)) + 1);
                };
            }
            have arena->occupied == old(region->arena->occupied) by {
                assumption();
            }
            have region->start == old(region->start) by {
                assumption();
            }
            have forall (k: int32) { old(region->start) <= k and k < i implies (let saved: int32* = old(region->arena->occupied); saved[k]) == 0 } by {
                intro();
                intro();
                extract(old(region->start) <= k);
                extract(k < i);
                instantiate(forall (j: int32) { region->start <= j and j < i implies arena->occupied[j] == 0 }, k) using {
                    old(region->start) <= k;
                    region->start == old(region->start);
                    k < i;
                };
                rewrite(old(region->arena->occupied) == arena->occupied);
                assumption();
            }
            let w = fold(arena_clear_window(old(region->arena->data), old(region->arena->occupied), old(region->arena->capacity), old(region->start), old(region->end)), { next: i });
            have region->start <= region->end by {
                assumption();
            }
            have region->arena == at(opened, region->arena) by {
                normalize() using {
                    at(cleared, region->arena) == at(opened, region->arena);
                };
            }
            have region->arena == old(region->arena) by {
                assumption();
            }
            have to_integer(i) == (to_integer(at(opened, i)) + 1) by {
                have -2147483648 <= (to_integer(at(opened, i)) + 1) by {
                    arithmetic_certificate {
                        negated_goal => (to_integer(at(opened, i)) + 1) < -2147483648;
                        premise 0: 0 <= to_integer(at(opened, i)) => 0 <= to_integer(at(opened, i));
                        add 0, 1 => (to_integer(at(opened, i)) + 1 + 0) < (-2147483648 +
                            to_integer(at(opened, i)));
                        conclusion 2;
                    }
                }
                have (to_integer(at(opened, i)) + 1) <= 2147483647 by {
                    arithmetic_certificate {
                        negated_goal => 2147483647 < (to_integer(at(opened, i)) + 1);
                        premise 0: to_integer(at(opened, i)) < to_integer(at(region(5).entry,
                            arena->capacity)) => to_integer(at(opened, i)) <
                            to_integer(at(region(5).entry, arena->capacity));
                        premise 1: to_integer(at(region(5).entry, arena->capacity)) <= 536870911 =>
                            to_integer(at(region(5).entry, arena->capacity)) <= 536870911;
                        add 0, 1 => (2147483647 + 1 + (to_integer(at(opened, i)) + 1)) <=
                            (to_integer(at(opened, i)) + 1 + to_integer(at(region(5).entry,
                            arena->capacity)));
                        add 3, 2 => (2147483647 + 1 + (to_integer(at(opened, i)) + 1) +
                            to_integer(at(region(5).entry, arena->capacity))) <=
                            (to_integer(at(opened, i)) + 1 + to_integer(at(region(5).entry,
                            arena->capacity)) + 536870911);
                        conclusion 4;
                    }
                }
                have to_integer(i) == (to_integer(at(opened, i)) + 1) by {
                    arithmetic_certificate rules {
                        premise 0: -2147483648 <= (to_integer(at(opened, i)) + 1) => -2147483648 <=
                            (to_integer(at(opened, i)) + 1);
                        premise 1: (to_integer(at(opened, i)) + 1) <= 2147483647 =>
                            (to_integer(at(opened, i)) + 1) <= 2147483647;
                        integer_operation_identity bounds [0, 1] => to_integer(i) ==
                            (to_integer(at(opened, i)) + 1);
                        conclusion 0;
                    }
                }
                assumption();
            }
            have 0 <= (to_integer(region->end) - to_integer(i)) by {
                arithmetic_certificate {
                    negated_goal => (to_integer(region->end) - to_integer(i)) < 0;
                    premise 0: to_integer(i) <= to_integer(old(region->end)) => to_integer(i) <=
                        to_integer(old(region->end));
                    premise 1: to_integer(region->end) == to_integer(old(region->end)) =>
                        to_integer(region->end) == to_integer(old(region->end));
                    less_equal_from_equal 2 reverse => to_integer(old(region->end)) <=
                        to_integer(region->end);
                    add 0, 1 => ((to_integer(region->end) - to_integer(i)) + to_integer(i)) < (0 +
                        to_integer(old(region->end)));
                    add 4, 3 => ((to_integer(region->end) - to_integer(i)) + to_integer(i) +
                        to_integer(old(region->end))) < (0 + to_integer(old(region->end)) +
                        to_integer(region->end));
                    conclusion 5;
                }
            }
            have (to_integer(region->end) - to_integer(i)) < (to_integer(region->end) - to_integer(at(opened, i))) by {
                rewrite(to_integer(i) == (to_integer(at(opened, i)) + 1));
                normalize();
            }
            have w.next == i by {
                normalize();
            }
            have w.next == i implies forall (k: int32) { 0 <= k and k < region->start implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } by {
                intro();
                assumption();
            }
            have w.next == i implies forall (k: int32) { 0 <= k and k < region->start implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } implies forall (k: int32) { region->end <= k and k < arena->capacity implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } by {
                intro();
                intro();
                assumption();
            }
            have w.next == i implies forall (k: int32) { 0 <= k and k < region->start implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } implies forall (k: int32) { region->end <= k and k < arena->capacity implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } implies arena->data == at(clear_occupied.entry, arena->data) by {
                intro();
                intro();
                intro();
                assumption();
            }
            have w.next == i implies forall (k: int32) { 0 <= k and k < region->start implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } implies forall (k: int32) { region->end <= k and k < arena->capacity implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } implies arena->data == at(clear_occupied.entry, arena->data) implies arena->occupied == at(clear_occupied.entry, arena->occupied) by {
                intro();
                intro();
                intro();
                intro();
                assumption();
            }
            have w.next == i implies forall (k: int32) { 0 <= k and k < region->start implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } implies forall (k: int32) { region->end <= k and k < arena->capacity implies arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]) } implies arena->data == at(clear_occupied.entry, arena->data) implies arena->occupied == at(clear_occupied.entry, arena->occupied) implies region->arena == old(region->arena) by {
                intro();
                intro();
                intro();
                intro();
                intro();
                assumption();
            }
        }
    }
    let { next: m } = unfold(w);
    have m <= region->end by {
        assumption();
    }
    have not i < region->end by {
        assumption();
    }
    have not m < region->end by {
        assumption();
    }
    have m == region->end by {
        arithmetic_certificate {
            premise 0: at(function.entry, m) <= at(function.entry, region->end) =>
                at(function.entry, m) <= at(function.entry, region->end);
            premise 1: not at(function.entry, m) < at(function.entry, region->end) => not
                at(function.entry, m) < at(function.entry, region->end);
            equal_from_bounds 0, 1 => m == region->end;
            conclusion 2;
        }
    }
    have region->start <= region->end by {
        assumption();
    }
    have 0 <= region->end by {
        arithmetic_certificate {
            premise 0: at(region(3).exit, i) <= m => at(region(3).exit, i) <= m;
            premise 1: at(function.entry, m) <= at(function.entry, region->end) =>
                at(function.entry, m) <= at(function.entry, region->end);
            add 0, 1 => (at(region(3).exit, to_integer((i as int32))) + at(function.entry,
                to_integer((m as int32)))) <= (to_integer((m as int32)) + at(function.entry,
                to_integer((region->end as int32))));
            premise 2: at(function.entry, 0) <= at(function.entry, region->start) =>
                at(function.entry, 0) <= at(function.entry, region->start);
            add 2, 3 => (at(region(3).exit, to_integer((i as int32))) + at(function.entry,
                to_integer((m as int32))) + at(function.entry, to_integer((0 as int32)))) <=
                (to_integer((m as int32)) + at(function.entry, to_integer((region->end as int32))) +
                at(function.entry, to_integer((region->start as int32))));
            conclusion 4;
        }
    }
    have region->end <= arena->capacity by {
        assumption();
    }
    have forall (k: int32) { region->start <= k and k < region->end implies arena->occupied[k] == 0 } by {
        intro();
        intro();
        extract(region->start <= k);
        extract(k < region->end);
        have k < m by {
            assumption();
        }
        instantiate(forall (j: int32) { region->start <= j and j < m implies arena->occupied[j] == 0 }, k) using {
            region->start <= k;
            k < m;
        };
    }
    have forall (k: int32) { 0 <= k and k < region->start implies arena->occupied[k] == old(region->arena->occupied[k]) } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < region->start);
        have arena->occupied[k] == old(region->arena->occupied[k]) by {
            instantiate(forall (j: int32) { 0 <= j and j < region->start implies arena->occupied[j] == at(clear_occupied.entry, arena->occupied[j]) }, k) using {
                0 <= k;
                k < region->start;
            };
        }
        have k < region->end by {
            arithmetic_certificate {
                premise 0: at(region(3).exit, i) <= m => at(region(3).exit, i) <= m;
                premise 1: at(function.entry, m) <= at(function.entry, region->end) =>
                    at(function.entry, m) <= at(function.entry, region->end);
                add 0, 1 => (at(region(3).exit, to_integer((i as int32))) + at(function.entry,
                    to_integer((m as int32)))) <= (to_integer((m as int32)) + at(function.entry,
                    to_integer((region->end as int32))));
                premise 2: k < at(region(3).exit, i) => k < at(region(3).exit, i);
                add 2, 3 => (at(region(3).exit, to_integer((i as int32))) + at(function.entry,
                    to_integer((m as int32))) + to_integer((k as int32))) < (to_integer((m as
                    int32)) + at(function.entry, to_integer((region->end as int32))) +
                    at(region(3).exit, to_integer((i as int32))));
                conclusion 4;
            }
        }
        have k < arena->capacity by {
            arithmetic_certificate {
                premise 0: at(function.entry, k) < at(function.entry, region->end) =>
                    at(function.entry, k) < at(function.entry, region->end);
                premise 1: at(function.entry, region->end) <= at(function.entry, arena->capacity) =>
                    at(function.entry, region->end) <= at(function.entry, arena->capacity);
                add 0, 1 => (at(function.entry, to_integer((k as int32))) + at(function.entry,
                    to_integer((region->end as int32)))) < (at(function.entry,
                    to_integer((region->end as int32))) + at(function.entry,
                    to_integer((arena->capacity as int32))));
                conclusion 2;
            }
        }
        instantiate(forall (j: int32) { at(clear_occupied.entry, 0) <= at(clear_occupied.entry, j) and at(clear_occupied.entry, j) < at(clear_occupied.entry, arena->capacity) implies at(clear_occupied.entry, arena->occupied[j]) == old(region->arena->occupied[j]) }, k) using {
            0 <= k;
            k < arena->capacity;
        };
        normalize() using {
            arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]);
            at(clear_occupied.entry, arena->occupied[k]) == old(region->arena->occupied[k]);
        };
    }
    have forall (k: int32) { region->end <= k and k < arena->capacity implies arena->occupied[k] == old(region->arena->occupied[k]) } by {
        intro();
        intro();
        extract(region->end <= k);
        extract(k < arena->capacity);
        have arena->occupied[k] == old(region->arena->occupied[k]) by {
            instantiate(forall (j: int32) { region->end <= j and j < arena->capacity implies arena->occupied[j] == at(clear_occupied.entry, arena->occupied[j]) }, k) using {
                region->end <= k;
                k < arena->capacity;
            };
        }
        have 0 <= k by {
            arithmetic_certificate {
                premise 0: at(function.entry, 0) <= at(function.entry, region->end) =>
                    at(function.entry, 0) <= at(function.entry, region->end);
                premise 1: at(region(0).entry, region->end) <= k => at(region(0).entry, region->end)
                    <= k;
                add 0, 1 => (at(function.entry, 0) + at(region(0).entry, to_integer((region->end as
                    int32)))) <= (at(function.entry, to_integer((region->end as int32))) +
                    to_integer((k as int32)));
                conclusion 2;
            }
        }
        instantiate(forall (j: int32) { at(clear_occupied.entry, 0) <= at(clear_occupied.entry, j) and at(clear_occupied.entry, j) < at(clear_occupied.entry, arena->capacity) implies at(clear_occupied.entry, arena->occupied[j]) == old(region->arena->occupied[j]) }, k) using {
            0 <= k;
            k < arena->capacity;
        };
        normalize() using {
            arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]);
            at(clear_occupied.entry, arena->occupied[k]) == old(region->arena->occupied[k]);
        };
    }
    mark cleared;
    have at(cleared, separate(memory(arena->live_regions), memory(region->arena))) by {
        assumption();
    }
    have at(cleared, separate(memory(arena->live_regions), memory(arena->data))) by {
        normalize();
    }
    have at(cleared, separate(memory(arena->live_regions), memory(arena->occupied))) by {
        normalize();
    }
    have 1 <= n by {
        assumption();
    }
    step();
    have separate(statement(5).footprint, memory(region->arena)) by {
        normalize() using {
            at(cleared, separate(memory(arena->live_regions), memory(region->arena)));
        };
    }
    have region->arena == at(cleared, region->arena) by {
        transport_certificate {
            premise 0: separate(statement(5).footprint, memory(region->arena)) => separate(statement(5).footprint, memory(region->arena));
            preserve 0 => region->arena == at(cleared, region->arena);
            conclusion 1;
        }
    }
    have separate(statement(5).footprint, memory(arena->data)) by {
        normalize() using {
            at(cleared, separate(memory(arena->live_regions), memory(arena->data)));
        };
    }
    have arena->data == at(cleared, arena->data) by {
        transport_certificate {
            premise 0: separate(statement(5).footprint, memory(arena->data)) => separate(statement(5).footprint, memory(arena->data));
            preserve 0 => arena->data == at(cleared, arena->data);
            conclusion 1;
        }
    }
    have separate(statement(5).footprint, memory(arena->occupied)) by {
        normalize() using {
            at(cleared, separate(memory(arena->live_regions), memory(arena->occupied)));
        };
    }
    have arena->occupied == at(cleared, arena->occupied) by {
        transport_certificate {
            premise 0: separate(statement(5).footprint, memory(arena->occupied)) => separate(statement(5).footprint, memory(arena->occupied));
            preserve 0 => arena->occupied == at(cleared, arena->occupied);
            conclusion 1;
        }
    }
    have forall (k: int32) { region->start <= k and k < region->end implies region->arena->occupied[k] == 0 } by {
        intro();
        intro();
        extract(region->start <= k);
        extract(k < region->end);
        have 0 <= k by {
            arithmetic_certificate {
                premise 0: at(function.entry, 0) <= at(function.entry, region->start) =>
                    at(function.entry, 0) <= at(function.entry, region->start);
                premise 1: at(region(3).exit, i) <= k => at(region(3).exit, i) <= k;
                add 0, 1 => (at(function.entry, to_integer((0 as int32))) + at(region(3).exit,
                    to_integer((i as int32)))) <= (at(function.entry, to_integer((region->start as
                    int32))) + to_integer((k as int32)));
                conclusion 2;
            }
        }
        have k < arena->capacity by {
            arithmetic_certificate {
                premise 0: k < at(region(0).entry, region->end) => k < at(region(0).entry,
                    region->end);
                premise 1: at(function.entry, region->end) <= at(function.entry, arena->capacity) =>
                    at(function.entry, region->end) <= at(function.entry, arena->capacity);
                add 0, 1 => (to_integer((k as int32)) + at(function.entry, to_integer((region->end
                    as int32)))) < (at(region(0).entry, to_integer((region->end as int32))) +
                    at(function.entry, to_integer((arena->capacity as int32))));
                conclusion 2;
            }
        }
        instantiate(forall (j: int32) { at(cleared, region->start) <= at(cleared, j) and at(cleared, j) < at(cleared, region->end) implies at(cleared, arena->occupied[j]) == at(cleared, 0) }, k) using {
            region->start <= k;
            k < region->end;
        };
        transport(at(cleared, arena->occupied[k]) == at(cleared, 0), region->arena->occupied[k] == 0) using {
            at(cleared, arena->occupied[k]) == at(cleared, 0);
            separate(memory(*arena), memory(arena->occupied[0..arena->capacity]));
            0 <= k;
            k < arena->capacity;
        };
    }
    have forall (k: int32) { 0 <= k and k < region->start implies region->arena->occupied[k] == old(region->arena->occupied[k]) } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < region->start);
        have k < region->end by {
            arithmetic_certificate {
                premise 0: at(region(3).exit, i) <= m => at(region(3).exit, i) <= m;
                premise 1: at(function.entry, m) <= at(function.entry, region->end) =>
                    at(function.entry, m) <= at(function.entry, region->end);
                add 0, 1 => (at(region(3).exit, to_integer((i as int32))) + at(function.entry,
                    to_integer((m as int32)))) <= (to_integer((m as int32)) + at(function.entry,
                    to_integer((region->end as int32))));
                premise 2: k < at(region(3).exit, i) => k < at(region(3).exit, i);
                add 2, 3 => (at(region(3).exit, to_integer((i as int32))) + at(function.entry,
                    to_integer((m as int32))) + to_integer((k as int32))) < (to_integer((m as
                    int32)) + at(function.entry, to_integer((region->end as int32))) +
                    at(region(3).exit, to_integer((i as int32))));
                conclusion 4;
            }
        }
        have k < arena->capacity by {
            arithmetic_certificate {
                premise 0: at(function.entry, k) < at(function.entry, region->end) =>
                    at(function.entry, k) < at(function.entry, region->end);
                premise 1: at(function.entry, region->end) <= at(function.entry, arena->capacity) =>
                    at(function.entry, region->end) <= at(function.entry, arena->capacity);
                add 0, 1 => (at(function.entry, to_integer((k as int32))) + at(function.entry,
                    to_integer((region->end as int32)))) < (at(function.entry,
                    to_integer((region->end as int32))) + at(function.entry,
                    to_integer((arena->capacity as int32))));
                conclusion 2;
            }
        }
        instantiate(forall (j: int32) { at(cleared, 0) <= at(cleared, j) and at(cleared, j) < at(cleared, region->start) implies at(cleared, arena->occupied[j]) == old(region->arena->occupied[j]) }, k) using {
            0 <= k;
            k < region->start;
        };
        transport(at(cleared, arena->occupied[k]) == old(region->arena->occupied[k]), region->arena->occupied[k] == old(region->arena->occupied[k])) using {
            at(cleared, arena->occupied[k]) == old(region->arena->occupied[k]);
            separate(memory(*arena), memory(arena->occupied[0..arena->capacity]));
            0 <= k;
            k < arena->capacity;
        };
    }
    have forall (k: int32) { region->end <= k and k < arena->capacity implies region->arena->occupied[k] == old(region->arena->occupied[k]) } by {
        intro();
        intro();
        extract(region->end <= k);
        extract(k < arena->capacity);
        have 0 <= k by {
            arithmetic_certificate {
                premise 0: at(function.entry, 0) <= at(function.entry, region->end) =>
                    at(function.entry, 0) <= at(function.entry, region->end);
                premise 1: at(region(0).entry, region->end) <= k => at(region(0).entry, region->end)
                    <= k;
                add 0, 1 => (at(function.entry, 0) + at(region(0).entry, to_integer((region->end as
                    int32)))) <= (at(function.entry, to_integer((region->end as int32))) +
                    to_integer((k as int32)));
                conclusion 2;
            }
        }
        instantiate(forall (j: int32) { at(cleared, region->end) <= at(cleared, j) and at(cleared, j) < at(cleared, arena->capacity) implies at(cleared, arena->occupied[j]) == old(region->arena->occupied[j]) }, k) using {
            region->end <= k;
            k < arena->capacity;
        };
        transport(at(cleared, arena->occupied[k]) == old(region->arena->occupied[k]), region->arena->occupied[k] == old(region->arena->occupied[k])) using {
            at(cleared, arena->occupied[k]) == old(region->arena->occupied[k]);
            separate(memory(*arena), memory(arena->occupied[0..arena->capacity]));
            0 <= k;
            k < arena->capacity;
        };
    }
    fold(arena_cells(arena->data, arena->occupied, arena->capacity));
    let after = fold(arena_state(arena), { live: (n - 1), capacity: c });
    step();
    assumption();
    have region->start == old(r.start) by {
        assumption();
    }
    have region->end == old(r.end) by {
        assumption();
    }
    have to_integer(after.live) == (to_integer(old(st.live)) - 1) by {
        have -2147483648 <= (to_integer(old(st.live)) - 1) by {
            arithmetic_certificate {
                negated_goal => (to_integer(old(st.live)) - 1) < -2147483648;
                premise 0: 0 <= to_integer(old(st.live)) => 0 <= to_integer(old(st.live));
                add 0, 1 => ((to_integer(old(st.live)) - 1) + 0) < (-2147483648 +
                    to_integer(old(st.live)));
                conclusion 2;
            }
        }
        have (to_integer(old(st.live)) - 1) <= 2147483647 by {
            arithmetic_certificate {
                negated_goal => 2147483647 < (to_integer(old(st.live)) - 1);
                type_range => to_integer(old(st.live)) <= 2147483647;
                add 0, 1 => (2147483647 + to_integer(old(st.live))) < ((to_integer(old(st.live)) -
                    1) + 2147483647);
                conclusion 2;
            }
        }
        have to_integer(after.live) == (to_integer(old(st.live)) - 1) by {
            arithmetic_certificate rules {
                premise 0: -2147483648 <= (to_integer(old(st.live)) - 1) => -2147483648 <=
                    (to_integer(old(st.live)) - 1);
                premise 1: (to_integer(old(st.live)) - 1) <= 2147483647 => (to_integer(old(st.live))
                    - 1) <= 2147483647;
                integer_operation_identity bounds [0, 1] => to_integer(after.live) ==
                    (to_integer(old(st.live)) - 1);
                conclusion 0;
            }
        }
        assumption();
    }
    have forall (k: int32) { region->start <= k and k < region->end implies region->arena->occupied[k] == 0 } by {
        assumption();
    }
    have forall (k: int32) { 0 <= k and k < region->start implies region->arena->occupied[k] == old(region->arena->occupied[k]) } by {
        assumption();
    }
    have forall (k: int32) { region->end <= k and k < region->arena->capacity implies region->arena->occupied[k] == old(region->arena->occupied[k]) } by {
        assumption();
    }
    assumption();
    normalize();
    assumption();
    assumption();
    assumption();
    normalize();
    normalize();
    assumption();
    assumption();
    assumption();
}

verifying "arena_write.c";

void arena_write(struct region* region, int32 index, int32 value) {
    owns r: arena_region(region);
    owns st: arena_state(old(region->arena));
    requires 0 <= index;
    requires defined(r.start + index) and r.start + index < r.end;
    requires r.end <= st.capacity;

    ensures r.start == old(r.start);
    ensures r.end == old(r.end);
    ensures st.capacity == old(st.capacity);
    ensures r.end <= st.capacity;
    ensures st.live == old(st.live);
    ensures region->arena == old(region->arena);
    ensures region->arena->capacity == old(region->arena->capacity);
    ensures region->arena->data == old(region->arena->data);
    ensures region->arena->data[region->start + index] == value;
    ensures region->arena->data[r.start + index] == value;
    ensures forall (k: int32) {
        0 <= k and k < region->arena->capacity implies
            region->arena->occupied[k] == old(region->arena->occupied[k])
    };
} by {
    let { live: n, capacity: c } = unfold(st);
    let { start: s, end: e } = unfold(r);
    have defined(s + index);
    have s + index < e;
    have s <= s + index;
    have s + index + 1 <= e;
    have region->start == s;
    have region->start + index + 1 <= e;
    have 0 <= region->start + index;
    have region->arena->capacity == c;
    have region->start + index < region->arena->capacity;
    have 0 <= to_integer(region->start + index);
    have to_integer(region->start + index) < to_integer(region->arena->capacity);
    have to_integer(s) <= to_integer(s + index);
    have to_integer(s + index) < to_integer(e);
    have separate(
        memory(*region),
        memory(*(region->arena->data + (region->start + index)))
    );
    have separate(memory(*region->arena), memory(region->arena->data[0..region->arena->capacity])) by solve();
    have separate(memory(*region->arena), memory(region->arena->occupied[0..region->arena->capacity])) by solve();
    mark w;
    step();
    have separate(statement(0).footprint, memory(region->arena)) by { normalize() using {}; }
    have region->arena == at(statement(0).entry, region->arena) by {
        transport_certificate {
            premise 0: separate(statement(0).footprint, memory(region->arena)) => separate(statement(0).footprint, memory(region->arena));
            preserve 0 => region->arena == at(statement(0).entry, region->arena);
            conclusion 1;
        }
    }
    have separate(statement(0).footprint, memory(region->arena->data)) by { normalize() using {}; }
    have region->arena->data == at(statement(0).entry, region->arena->data) by {
        transport_certificate {
            premise 0: separate(statement(0).footprint, memory(region->arena->data)) => separate(statement(0).footprint, memory(region->arena->data));
            preserve 0 => region->arena->data == at(statement(0).entry, region->arena->data);
            conclusion 1;
        }
    }
    have separate(statement(0).footprint, memory(region->arena->occupied)) by { normalize() using {}; }
    have region->arena->occupied == at(statement(0).entry, region->arena->occupied) by {
        transport_certificate {
            premise 0: separate(statement(0).footprint, memory(region->arena->occupied)) => separate(statement(0).footprint, memory(region->arena->occupied));
            preserve 0 => region->arena->occupied == at(statement(0).entry, region->arena->occupied);
            conclusion 1;
        }
    }
    step();
    have separate(statement(1).footprint, memory(region->arena)) by { normalize() using {}; }
    have region->arena == at(statement(1).entry, region->arena) by {
        transport_certificate {
            premise 0: separate(statement(1).footprint, memory(region->arena)) => separate(statement(1).footprint, memory(region->arena));
            preserve 0 => region->arena == at(statement(1).entry, region->arena);
            conclusion 1;
        }
    }
    have separate(statement(1).footprint, memory(region->arena->data)) by { normalize() using {}; }
    have region->arena->data == at(statement(1).entry, region->arena->data) by {
        transport_certificate {
            premise 0: separate(statement(1).footprint, memory(region->arena->data)) => separate(statement(1).footprint, memory(region->arena->data));
            preserve 0 => region->arena->data == at(statement(1).entry, region->arena->data);
            conclusion 1;
        }
    }
    have separate(statement(1).footprint, memory(region->arena->occupied)) by { normalize() using {}; }
    have region->arena->occupied == at(statement(1).entry, region->arena->occupied) by {
        transport_certificate {
            premise 0: separate(statement(1).footprint, memory(region->arena->occupied)) => separate(statement(1).footprint, memory(region->arena->occupied));
            preserve 0 => region->arena->occupied == at(statement(1).entry, region->arena->occupied);
            conclusion 1;
        }
    }
    mark before_access;
    have at(before_access, separate(memory(region->arena->data[region->start + index]), memory(region->arena)));
    have at(before_access, separate(memory(region->arena->data[region->start + index]), memory(region->arena->data)));
    have at(before_access, separate(memory(region->arena->data[region->start + index]), memory(region->arena->occupied)));
    have at(before_access, separate(memory(region->arena->data[region->start + index]), memory(region->arena->capacity)));
    step();
    have separate(statement(2).footprint, memory(region->arena->capacity)) by {
        normalize() using { at(before_access, separate(memory(region->arena->data[region->start + index]), memory(region->arena->capacity))); };
    }
    have region->arena->capacity == at(before_access, region->arena->capacity) by {
        transport_certificate {
            premise 0: separate(statement(2).footprint, memory(region->arena->capacity)) => separate(statement(2).footprint, memory(region->arena->capacity));
            preserve 0 => region->arena->capacity == at(before_access, region->arena->capacity);
            conclusion 1;
        }
    }
    have separate(statement(2).footprint, memory(region->arena)) by { normalize() using { at(before_access, separate(memory(region->arena->data[region->start + index]), memory(region->arena))); }; }
    have region->arena == at(before_access, region->arena) by {
        transport_certificate {
            premise 0: separate(statement(2).footprint, memory(region->arena)) => separate(statement(2).footprint, memory(region->arena));
            preserve 0 => region->arena == at(before_access, region->arena);
            conclusion 1;
        }
    }
    have separate(statement(2).footprint, memory(region->arena->data)) by { normalize() using { at(before_access, separate(memory(region->arena->data[region->start + index]), memory(region->arena->data))); }; }
    have region->arena->data == at(before_access, region->arena->data) by {
        transport_certificate {
            premise 0: separate(statement(2).footprint, memory(region->arena->data)) => separate(statement(2).footprint, memory(region->arena->data));
            preserve 0 => region->arena->data == at(before_access, region->arena->data);
            conclusion 1;
        }
    }
    have separate(statement(2).footprint, memory(region->arena->occupied)) by { normalize() using { at(before_access, separate(memory(region->arena->data[region->start + index]), memory(region->arena->occupied))); }; }
    have region->arena->occupied == at(before_access, region->arena->occupied) by {
        transport_certificate {
            premise 0: separate(statement(2).footprint, memory(region->arena->occupied)) => separate(statement(2).footprint, memory(region->arena->occupied));
            preserve 0 => region->arena->occupied == at(before_access, region->arena->occupied);
            conclusion 1;
        }
    }

    have region->arena == old(region->arena);
    have region->arena->data == old(region->arena->data);

    have forall (k: int32) {
        0 <= k and k < at(w, region->arena->capacity) implies
            at(w, region->arena->occupied[k]) == region->arena->occupied[k]
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < at(w, region->arena->capacity));
        transport(
            at(w, region->arena->occupied[k]) == at(w, region->arena->occupied[k]),
            at(w, region->arena->occupied[k]) == region->arena->occupied[k]
        ) using {
            0 <= k;
            k < at(w, region->arena->capacity);
            separate(memory(region->arena->occupied[0..region->arena->capacity]),
                memory(region->arena->data[0..region->arena->capacity]));
        };
        assumption();
    }
    have region->arena->capacity == old(region->arena->capacity) by solve();
    have separate(memory(*region->arena), memory(region->arena->data[0..region->arena->capacity])) by {
        rewrite(region->arena->capacity == old(region->arena->capacity));
        rewrite(region->arena->data == old(region->arena->data));
        rewrite(region->arena == old(region->arena));
        assumption();
    }
    have region->arena->occupied == old(region->arena->occupied) by solve();
    have separate(memory(*region->arena), memory(region->arena->occupied[0..region->arena->capacity])) by {
        rewrite(region->arena->capacity == old(region->arena->capacity));
        rewrite(region->arena->occupied == old(region->arena->occupied));
        rewrite(region->arena == old(region->arena));
        assumption();
    }
    have separate(memory(region->arena->occupied[0..region->arena->capacity]), memory(region->arena->data[0..region->arena->capacity])) by {
        rewrite(region->arena->capacity == old(region->arena->capacity));
        rewrite(region->arena->occupied == old(region->arena->occupied));
        rewrite(region->arena->data == old(region->arena->data));
        assumption();
    }
    let r = fold(arena_region(region), { start: s, end: e });
    let st = fold(arena_state(region->arena), { live: n, capacity: c });
    step_until(function.exit);
    solve();
}

verifying "arena_read.c";

int32 arena_read(struct region* region, int32 index) {
    owns r: arena_region(region);
    owns st: arena_state(old(region->arena));
    requires 0 <= index;
    requires defined(r.start + index) and r.start + index < r.end;
    requires r.end <= st.capacity;

    ensures r.start == old(r.start);
    ensures r.end == old(r.end);
    ensures st.capacity == old(st.capacity);
    ensures r.end <= st.capacity;
    ensures st.live == old(st.live);
    ensures region->arena == old(region->arena);
    ensures region->arena->capacity == old(region->arena->capacity);
    ensures region->arena->data == old(region->arena->data);
    ensures result == region->arena->data[region->start + index];
    ensures result == old(region->arena->data[region->start + index]);
    ensures result == old(region->arena->data[r.start + index]);
    ensures forall (k: int32) {
        0 <= k and k < region->arena->capacity implies
            region->arena->occupied[k] == old(region->arena->occupied[k])
    };
} by {
    let { live: n, capacity: c } = unfold(st);
    let { start: s, end: e } = unfold(r);
    have defined(s + index);
    have s + index < e;
    have s <= s + index;
    have s + index + 1 <= e;
    have region->start + index + 1 <= e;
    have s + index < c;
    have region->start + index < region->arena->capacity;
    have 0 <= to_integer(region->start + index);
    have to_integer(region->start + index) < to_integer(region->arena->capacity);
    have to_integer(s) <= to_integer(s + index);
    have to_integer(s + index) < to_integer(e);
    mark w;
    step();
    have separate(statement(0).footprint, memory(region->arena)) by { normalize() using {}; }
    have region->arena == at(statement(0).entry, region->arena) by {
        transport_certificate {
            premise 0: separate(statement(0).footprint, memory(region->arena)) => separate(statement(0).footprint, memory(region->arena));
            preserve 0 => region->arena == at(statement(0).entry, region->arena);
            conclusion 1;
        }
    }
    have separate(statement(0).footprint, memory(region->arena->data)) by { normalize() using {}; }
    have region->arena->data == at(statement(0).entry, region->arena->data) by {
        transport_certificate {
            premise 0: separate(statement(0).footprint, memory(region->arena->data)) => separate(statement(0).footprint, memory(region->arena->data));
            preserve 0 => region->arena->data == at(statement(0).entry, region->arena->data);
            conclusion 1;
        }
    }
    have separate(statement(0).footprint, memory(region->arena->occupied)) by { normalize() using {}; }
    have region->arena->occupied == at(statement(0).entry, region->arena->occupied) by {
        transport_certificate {
            premise 0: separate(statement(0).footprint, memory(region->arena->occupied)) => separate(statement(0).footprint, memory(region->arena->occupied));
            preserve 0 => region->arena->occupied == at(statement(0).entry, region->arena->occupied);
            conclusion 1;
        }
    }
    step();
    have separate(statement(1).footprint, memory(region->arena)) by { normalize() using {}; }
    have region->arena == at(statement(1).entry, region->arena) by {
        transport_certificate {
            premise 0: separate(statement(1).footprint, memory(region->arena)) => separate(statement(1).footprint, memory(region->arena));
            preserve 0 => region->arena == at(statement(1).entry, region->arena);
            conclusion 1;
        }
    }
    have separate(statement(1).footprint, memory(region->arena->data)) by { normalize() using {}; }
    have region->arena->data == at(statement(1).entry, region->arena->data) by {
        transport_certificate {
            premise 0: separate(statement(1).footprint, memory(region->arena->data)) => separate(statement(1).footprint, memory(region->arena->data));
            preserve 0 => region->arena->data == at(statement(1).entry, region->arena->data);
            conclusion 1;
        }
    }
    have separate(statement(1).footprint, memory(region->arena->occupied)) by { normalize() using {}; }
    have region->arena->occupied == at(statement(1).entry, region->arena->occupied) by {
        transport_certificate {
            premise 0: separate(statement(1).footprint, memory(region->arena->occupied)) => separate(statement(1).footprint, memory(region->arena->occupied));
            preserve 0 => region->arena->occupied == at(statement(1).entry, region->arena->occupied);
            conclusion 1;
        }
    }
    mark before_access;
    step();
    have region->arena == at(before_access, region->arena) by { assumption(); }
    have region->arena->data == at(before_access, region->arena->data) by { assumption(); }
    have region->arena->occupied == at(before_access, region->arena->occupied) by { assumption(); }
    have forall (k: int32) {
        0 <= k and k < at(w, region->arena->capacity) implies
            at(w, region->arena->occupied[k]) == region->arena->occupied[k]
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < at(w, region->arena->capacity));
        solve();
    }
    let r = fold(arena_region(region), { start: s, end: e });
    let st = fold(arena_state(region->arena), { live: n, capacity: c });
    solve();
}

verifying "arena_destroy.c";

void arena_destroy(struct arena* arena) {
    consumes st: arena_state(arena);
    requires forall (k: int32) {
        0 <= k and k < arena->capacity implies arena->occupied[k] == 0
    };
    produces *arena;

    ensures arena->data == 0;
    ensures arena->occupied == 0;
    ensures arena->capacity == 0;
    ensures arena->live_regions == 0;
} by {
    let { live: n } = unfold(st);
    unfold(arena_initialized_storage(
        arena->data,
        arena->occupied,
        arena->capacity,
        1
    ));
    unfold(arena_cells(arena->data, arena->occupied, arena->capacity));
    scatter(arena_cells(arena->data, arena->occupied, arena->capacity));
    step_until(function.exit);
    solve();
}

verifying "arena_region_length.c";

int32 arena_region_length(struct region* region) {
    owns r: arena_region(region);
    owns st: arena_state(old(region->arena));
    ensures result == r.end - r.start;
    ensures st.live == old(st.live);
    ensures r.start == old(r.start);
    ensures r.end == old(r.end);
} by {
    let { live: n } = unfold(st);
    let { start: s, end: e } = unfold(r);
    have region->start == s by assumption();
    step_until(function.exit);
    have result == e - s;
    let r = fold(arena_region(region), { start: s, end: e });
    let st = fold(arena_state(region->arena), { live: n, capacity: region->arena->capacity });
    solve();
}

verifying "arena_pipeline.c";

int32 arena_pipeline(
    struct arena* arena,
    struct region* first,
    struct region* second,
    struct region* combined
) {
    owns *arena;
    owns *first;
    owns *second;
    owns *combined;

    ensures result == 0 or result == 33;
} by {
    step();
    step();
    step();
    step();
    step();
    let { outcome: o0 } = step(arena_init, {});
    if at(region(6).entry, initialized) == at(region(6).entry, 0) {
        step();
        have o0.model == ArenaInitOutcome::Failure() by {
            extract(o0.model == ArenaInitOutcome::Failure());
        }
        unfold(o0);
        step();
        assumption();
        have result == 0 or result == 33 by {
            transport(at(function.exit, result == 0 or result == 33), result == 0 or result == 33) using {
            };
        }
        assumption();
        assumption();
        assumption();
        assumption();
    } else {
        step();
        step();
    }
    have initialized == 1 by {
        cases {
            initialized == 0 => {
                contradiction(initialized == 0);
            }
            initialized == 1 => {
                assumption();
            }
        }
    }
    have o0.model == ArenaInitOutcome::Success(0, 8) by {
        extract(o0.model == ArenaInitOutcome::Success(0, 8));
    }
    let { state: s0 } = unfold(o0);
    have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == 0 } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        instantiate(forall (j: int32) { initialized == 1 and 0 <= j and j < arena->capacity implies arena->occupied[j] == 0 }, k) using {
            initialized == 1;
            0 <= k;
            k < arena->capacity;
        };
    }
    mark a1;
    let { outcome: o1 } = step(arena_alloc, { st: s0 });
    have allocated == 1 implies first->arena == arena by {
        assumption();
    }
    have arena->capacity == at(a1, arena->capacity) by {
        assumption();
    }
    if at(region(10).entry, allocated) == at(region(10).entry, 0) {
        step();
        have o1.model == ArenaAllocOutcome::Failure() by {
            extract(o1.model == ArenaAllocOutcome::Failure());
        }
        have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == 0 } by {
            intro();
            intro();
            extract(0 <= k);
            extract(k < arena->capacity);
            have arena->occupied[k] == at(a1, arena->occupied[k]) by {
                instantiate(forall (j: int32) { allocated == 0 and 0 <= j and j < arena->capacity implies arena->occupied[j] == at(a1, arena->occupied[j]) }, k) using {
                    allocated == 0;
                    0 <= k;
                    k < arena->capacity;
                };
            }
            have k < at(a1, arena->capacity) by {
                assumption();
            }
            have at(a1, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) { 0 <= j and j < at(a1, arena->capacity) implies at(a1, arena->occupied[j]) == 0 }, k) using {
                    0 <= k;
                    k < at(a1, arena->capacity);
                };
            }
            assumption();
        }
        step(arena_destroy, { st: s0 });
        unfold(o1);
        step();
        assumption();
        have result == 0 or result == 33 by {
            assumption();
        }
        assumption();
        assumption();
        assumption();
        assumption();
    } else {
        step();
        step();
    }
    have allocated == 1 by {
        cases {
            allocated == 0 => {
                contradiction(allocated == 0);
            }
            allocated == 1 => {
                assumption();
            }
        }
    }
    have o1.model == ArenaAllocOutcome::Success(first->start, first->end) by {
        extract(o1.model == ArenaAllocOutcome::Success(first->start, first->end));
    }
    have first->end <= arena->capacity by {
        extract(first->end <= arena->capacity);
    }
    let { allocated: r1 } = unfold(o1);
    have first->arena == arena by {
        extract(first->arena == arena);
    }
    mark z1;
    have r1.start == at(z1, first->start) by {
        normalize();
    }
    have r1.end == at(z1, first->end) by {
        normalize();
    }
    have forall (k: int32) { 0 <= k and k < arena->capacity and (k < at(z1, first->start) or at(z1, first->end) <= k) implies arena->occupied[k] == 0 } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        extract(k < at(z1, first->start) or at(z1, first->end) <= k);
        have k < at(a1, arena->capacity) by {
            assumption();
        }
        have at(a1, arena->occupied[k]) == 0 by {
            instantiate(forall (j: int32) { 0 <= j and j < at(a1, arena->capacity) implies at(a1, arena->occupied[j]) == 0 }, k) using {
                0 <= k;
                k < at(a1, arena->capacity);
            };
        }
        cases {
            k < at(z1, first->start) => {
                have k < first->start by {
                    assumption();
                }
                have arena->occupied[k] == at(a1, arena->occupied[k]) by {
                    instantiate(forall (j: int32) { allocated == 1 and 0 <= j and j < first->start implies arena->occupied[j] == at(a1, arena->occupied[j]) }, k) using {
                        allocated == 1;
                        0 <= k;
                        k < first->start;
                    };
                }
                assumption();
            }
            at(z1, first->end) <= k => {
                have first->end <= k by {
                    assumption();
                }
                have arena->occupied[k] == at(a1, arena->occupied[k]) by {
                    instantiate(forall (j: int32) { allocated == 1 and first->end <= j and j < arena->capacity implies arena->occupied[j] == at(a1, arena->occupied[j]) }, k) using {
                        allocated == 1;
                        first->end <= k;
                        k < arena->capacity;
                    };
                }
                assumption();
            }
        }
    }
    have at(a1, s0.live) == 0 by {
        normalize();
    }
    have s0.live == 1 by {
        assumption();
    }
    mark a2;
    let { outcome: o2 } = step(arena_alloc, { st: s0 });
    have allocated == 1 implies second->arena == arena by {
        assumption();
    }
    have arena->capacity == at(a2, arena->capacity) by {
        assumption();
    }
    if at(region(15).entry, allocated) == at(region(15).entry, 0) {
        step();
        have o2.model == ArenaAllocOutcome::Failure() by {
            extract(o2.model == ArenaAllocOutcome::Failure());
        }
        have forall (k: int32) { 0 <= k and k < arena->capacity and (k < at(z1, first->start) or at(z1, first->end) <= k) implies arena->occupied[k] == 0 } by {
            intro();
            intro();
            extract(0 <= k);
            extract(k < arena->capacity);
            extract(k < at(z1, first->start) or at(z1, first->end) <= k);
            have arena->occupied[k] == at(a2, arena->occupied[k]) by {
                instantiate(forall (j: int32) { allocated == 0 and 0 <= j and j < arena->capacity implies arena->occupied[j] == at(a2, arena->occupied[j]) }, k) using {
                    allocated == 0;
                    0 <= k;
                    k < arena->capacity;
                };
            }
            have k < at(a2, arena->capacity) by {
                assumption();
            }
            have at(a2, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) { 0 <= j and j < at(a2, arena->capacity) and (j < at(z1, first->start) or at(z1, first->end) <= j) implies at(a2, arena->occupied[j]) == 0 }, k) using {
                    0 <= k;
                    k < at(a2, arena->capacity);
                    k < at(z1, first->start) or at(z1, first->end) <= k;
                };
            }
            assumption();
        }
        have at(a2, s0.live) == 1 by {
            assumption();
        }
        have s0.live == 1 by {
            assumption();
        }
        have r1.end <= at(z1, arena->capacity) by {
            assumption();
        }
        have s0.capacity == arena->capacity by {
            assumption();
        }
        have r1.end <= s0.capacity by {
            assumption();
        }
        have 1 <= s0.live by {
            arithmetic_certificate signed_int32 {
                premise 0: (at(region(16).entry, s0.live) as int32) == (at(region(16).entry, 1) as
                    int32) => (at(region(16).entry, s0.live) as int32) == (at(region(16).entry, 1)
                    as int32);
                less_equal_from_equal 0 reverse => to_integer((at(region(16).entry, 1) as int32)) <=
                    to_integer((at(region(16).entry, s0.live) as int32));
                conclusion 1;
            }
        }
        have first->arena == arena by {
            assumption();
        }
        mark f1;
        let { after: g1 } = step(arena_free, { r: r1, st: s0 });
        have first->arena == arena by {
            assumption();
        }
        have first->arena->capacity == at(f1, first->arena->capacity) by {
            assumption();
        }
        have arena->capacity == first->arena->capacity by {
            assumption();
        }
        have at(f1, first->arena->capacity) == at(f1, arena->capacity) by {
            assumption();
        }
        have arena->capacity == at(f1, arena->capacity) by {
            assumption();
        }
        have first->start == at(z1, first->start) by {
            assumption();
        }
        have first->end == at(z1, first->end) by {
            assumption();
        }
        have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == 0 } by {
            intro();
            intro();
            extract(0 <= k);
            extract(k < arena->capacity);
            have k < first->start implies arena->occupied[k] == 0 by {
                intro();
                have first->arena->occupied[k] == at(f1, first->arena->occupied[k]) by {
                    instantiate(forall (j: int32) { 0 <= j and j < first->start implies first->arena->occupied[j] == at(f1, first->arena->occupied[j]) }, k) using {
                        0 <= k;
                        k < first->start;
                    };
                }
                have at(f1, first->arena->occupied[k]) == at(f1, arena->occupied[k]) by {
                    assumption();
                }
                have k < at(f1, arena->capacity) by {
                    assumption();
                }
                have k < at(z1, first->start) by {
                    assumption();
                }
                have k < at(z1, first->start) or at(z1, first->end) <= k by {
                    assumption();
                }
                have at(f1, arena->occupied[k]) == 0 by {
                    instantiate(forall (j: int32) { 0 <= j and j < at(f1, arena->capacity) and (j < at(z1, first->start) or at(z1, first->end) <= j) implies at(f1, arena->occupied[j]) == 0 }, k) using {
                        0 <= k;
                        k < at(f1, arena->capacity);
                        k < at(z1, first->start) or at(z1, first->end) <= k;
                    };
                }
                normalize() using {
                    first->arena == arena;
                    first->arena->occupied[k] == at(f1, first->arena->occupied[k]);
                    at(f1, first->arena->occupied[k]) == at(f1, arena->occupied[k]);
                    at(f1, arena->occupied[k]) == 0;
                };
            }
            have first->start <= k and k < first->end implies arena->occupied[k] == 0 by {
                intro();
                extract(first->start <= k);
                extract(k < first->end);
                have arena->occupied[k] == 0 by {
                    instantiate(forall (j: int32) { first->start <= j and j < first->end implies first->arena->occupied[j] == 0 }, k) using {
                        first->start <= k;
                        k < first->end;
                    };
                    normalize() using {
                        first->arena == arena;
                        first->arena->occupied[k] == 0;
                    };
                }
                assumption();
            }
            have first->end <= k implies arena->occupied[k] == 0 by {
                intro();
                have k < first->arena->capacity by {
                    assumption();
                }
                have first->arena->occupied[k] == at(f1, first->arena->occupied[k]) by {
                    instantiate(forall (j: int32) { first->end <= j and j < first->arena->capacity implies first->arena->occupied[j] == at(f1, first->arena->occupied[j]) }, k) using {
                        first->end <= k;
                        k < first->arena->capacity;
                    };
                }
                have at(f1, first->arena->occupied[k]) == at(f1, arena->occupied[k]) by {
                    assumption();
                }
                have k < at(f1, arena->capacity) by {
                    assumption();
                }
                have at(z1, first->end) <= k by {
                    assumption();
                }
                have k < at(z1, first->start) or at(z1, first->end) <= k by {
                    assumption();
                }
                have at(f1, arena->occupied[k]) == 0 by {
                    instantiate(forall (j: int32) { 0 <= j and j < at(f1, arena->capacity) and (j < at(z1, first->start) or at(z1, first->end) <= j) implies at(f1, arena->occupied[j]) == 0 }, k) using {
                        0 <= k;
                        k < at(f1, arena->capacity);
                        k < at(z1, first->start) or at(z1, first->end) <= k;
                    };
                }
                normalize() using {
                    first->arena == arena;
                    first->arena->occupied[k] == at(f1, first->arena->occupied[k]);
                    at(f1, first->arena->occupied[k]) == at(f1, arena->occupied[k]);
                    at(f1, arena->occupied[k]) == 0;
                };
            }
            if k < first->start {
                have k < first->start by {
                    assumption();
                }
                extract(arena->occupied[k] == 0);
            } else {
                have first->start <= k by {
                    assumption();
                }
                if k < first->end {
                    have first->start <= k and k < first->end by {
                        assumption();
                    }
                    extract(arena->occupied[k] == 0);
                } else {
                    have first->end <= k by {
                        assumption();
                    }
                    extract(arena->occupied[k] == 0);
                }
            }
        }
        step(arena_destroy, { st: g1 });
        unfold(o2);
        step();
        assumption();
        have result == 0 or result == 33 by {
            assumption();
        }
        assumption();
        assumption();
        assumption();
        assumption();
    } else {
        step();
        step();
    }
    have allocated == 1 by {
        cases {
            allocated == 0 => {
                contradiction(allocated == 0);
            }
            allocated == 1 => {
                assumption();
            }
        }
    }
    have o2.model == ArenaAllocOutcome::Success(second->start, second->end) by {
        extract(o2.model == ArenaAllocOutcome::Success(second->start, second->end));
    }
    have second->end <= arena->capacity by {
        extract(second->end <= arena->capacity);
    }
    let { allocated: r2 } = unfold(o2);
    have second->arena == arena by {
        extract(second->arena == arena);
    }
    have at(a2, s0.live) == 1 by {
        assumption();
    }
    have s0.live == 2 by {
        assumption();
    }
    mark z2;
    have r2.start == at(z2, second->start) by {
        normalize();
    }
    have r2.end == at(z2, second->end) by {
        normalize();
    }
    have forall (k: int32) { 0 <= k and k < arena->capacity and (k < at(z1, first->start) or at(z1, first->end) <= k) and (k < at(z2, second->start) or at(z2, second->end) <= k) implies arena->occupied[k] == 0 } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        extract(k < at(z1, first->start) or at(z1, first->end) <= k);
        extract(k < at(z2, second->start) or at(z2, second->end) <= k);
        have k < at(a2, arena->capacity) by {
            assumption();
        }
        have at(a2, arena->occupied[k]) == 0 by {
            instantiate(forall (j: int32) { 0 <= j and j < at(a2, arena->capacity) and (j < at(z1, first->start) or at(z1, first->end) <= j) implies at(a2, arena->occupied[j]) == 0 }, k) using {
                0 <= k;
                k < at(a2, arena->capacity);
                k < at(z1, first->start) or at(z1, first->end) <= k;
            };
        }
        cases {
            k < at(z2, second->start) => {
                have k < second->start by {
                    assumption();
                }
                have arena->occupied[k] == at(a2, arena->occupied[k]) by {
                    instantiate(forall (j: int32) { allocated == 1 and 0 <= j and j < second->start implies arena->occupied[j] == at(a2, arena->occupied[j]) }, k) using {
                        allocated == 1;
                        0 <= k;
                        k < second->start;
                    };
                }
                assumption();
            }
            at(z2, second->end) <= k => {
                have second->end <= k by {
                    assumption();
                }
                have arena->occupied[k] == at(a2, arena->occupied[k]) by {
                    instantiate(forall (j: int32) { allocated == 1 and second->end <= j and j < arena->capacity implies arena->occupied[j] == at(a2, arena->occupied[j]) }, k) using {
                        allocated == 1;
                        second->end <= k;
                        k < arena->capacity;
                    };
                }
                assumption();
            }
        }
    }
    have first->arena == arena by {
        assumption();
    }
    have r1.start < r1.end by {
        extract(r1.start < r1.end);
    }
    have r1.end <= at(z1, arena->capacity) by {
        assumption();
    }
    have s0.capacity == arena->capacity by {
        assumption();
    }
    have arena->capacity == at(z1, arena->capacity) by {
        assumption();
    }
    have r1.end <= s0.capacity by {
        assumption();
    }
    have first->arena == arena by {
        assumption();
    }
    mark w1;
    step(arena_write, { r: r1, st: s0 }) {
        requires 0 <= 0 by normalize();
        requires r1.end <= s0.capacity by assumption();
        requires defined(r1.start + 0) and (to_integer(r1.start) + to_integer(0)) < to_integer(r1.end) by {
            both {
                normalize();
            } and {
                arithmetic_certificate {
                    negated_goal => to_integer(r1.end) <= (to_integer(r1.start) + to_integer(0));
                    premise 0: to_integer(r1.start) < to_integer(r1.end) => to_integer(r1.start) <
                        to_integer(r1.end);
                    add 0, 1 => (to_integer(r1.end) + to_integer(r1.start)) < (to_integer(r1.start) +
                        to_integer(0) + to_integer(r1.end));
                    conclusion 2;
                }
            }
        }
    }
    have r1.start == at(w1, r1.start) by {
        assumption();
    }
    have at(w1, r1.start) == at(z1, first->start) by {
        normalize();
    }
    have r1.start == at(z1, first->start) by {
        normalize() using {
            r1.start == at(w1, r1.start);
            at(w1, r1.start) == at(z1, first->start);
        };
    }
    have r1.end == at(w1, r1.end) by {
        assumption();
    }
    have at(w1, r1.end) == at(z1, first->end) by {
        normalize();
    }
    have r1.end == at(z1, first->end) by {
        normalize() using {
            r1.end == at(w1, r1.end);
            at(w1, r1.end) == at(z1, first->end);
        };
    }
    have s0.live == at(w1, s0.live) by {
        assumption();
    }
    have at(w1, s0.live) == 2 by {
        assumption();
    }
    have s0.live == 2 by {
        normalize() using {
            s0.live == at(w1, s0.live);
            at(w1, s0.live) == 2;
        };
    }
    have r2.start == at(w1, r2.start) by {
        normalize();
    }
    have at(w1, r2.start) == at(z2, second->start) by {
        normalize();
    }
    have r2.start == at(z2, second->start) by {
        normalize() using {
            r2.start == at(w1, r2.start);
            at(w1, r2.start) == at(z2, second->start);
        };
    }
    have r2.end == at(w1, r2.end) by {
        normalize();
    }
    have at(w1, r2.end) == at(z2, second->end) by {
        normalize();
    }
    have r2.end == at(z2, second->end) by {
        normalize() using {
            r2.end == at(w1, r2.end);
            at(w1, r2.end) == at(z2, second->end);
        };
    }
    have first->arena == arena by {
        assumption();
    }
    have first->arena->capacity == at(w1, first->arena->capacity) by {
        assumption();
    }
    have arena->capacity == first->arena->capacity by {
        assumption();
    }
    have at(w1, first->arena->capacity) == at(w1, arena->capacity) by {
        assumption();
    }
    have arena->capacity == at(w1, arena->capacity) by {
        assumption();
    }
    have forall (k: int32) { 0 <= k and k < arena->capacity and (k < at(z1, first->start) or at(z1, first->end) <= k) and (k < at(z2, second->start) or at(z2, second->end) <= k) implies arena->occupied[k] == 0 } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        extract(k < at(z1, first->start) or at(z1, first->end) <= k);
        extract(k < at(z2, second->start) or at(z2, second->end) <= k);
        have k < first->arena->capacity by {
            assumption();
        }
        have first->arena->occupied[k] == at(w1, first->arena->occupied[k]) by {
            instantiate(forall (j: int32) { 0 <= j and j < first->arena->capacity implies first->arena->occupied[j] == at(w1, first->arena->occupied[j]) }, k) using {
                0 <= k;
                k < first->arena->capacity;
            };
        }
        have at(w1, first->arena->occupied[k]) == at(w1, arena->occupied[k]) by {
            assumption();
        }
        have k < at(w1, arena->capacity) by {
            assumption();
        }
        have at(w1, arena->occupied[k]) == 0 by {
            instantiate(forall (j: int32) { 0 <= j and j < at(w1, arena->capacity) and (j < at(z1, first->start) or at(z1, first->end) <= j) and (j < at(z2, second->start) or at(z2, second->end) <= j) implies at(w1, arena->occupied[j]) == 0 }, k) using {
                0 <= k;
                k < at(w1, arena->capacity);
                k < at(z1, first->start) or at(z1, first->end) <= k;
                k < at(z2, second->start) or at(z2, second->end) <= k;
            };
        }
        normalize() using {
            first->arena->occupied[k] == at(w1, first->arena->occupied[k]);
            at(w1, first->arena->occupied[k]) == at(w1, arena->occupied[k]);
            at(w1, arena->occupied[k]) == 0;
            first->arena == arena;
        };
    }
    have second->arena == arena by {
        assumption();
    }
    have r2.start < r2.end by {
        extract(r2.start < r2.end);
    }
    have r2.end <= at(z2, arena->capacity) by {
        assumption();
    }
    have s0.capacity == at(w1, s0.capacity) by {
        assumption();
    }
    have at(w1, s0.capacity) == at(w1, arena->capacity) by {
        assumption();
    }
    have s0.capacity == arena->capacity by {
        assumption();
    }
    have arena->capacity == at(z2, arena->capacity) by {
        assumption();
    }
    have r2.end <= s0.capacity by {
        assumption();
    }
    have first->arena->data == second->arena->data by {
        assumption();
    }
    mark w2;
    step(arena_write, { r: r2, st: s0 }) {
        requires 0 <= 0 by normalize();
        requires r2.end <= s0.capacity by assumption();
        requires defined(r2.start + 0) and (to_integer(r2.start) + to_integer(0)) < to_integer(r2.end) by {
            both {
                normalize();
            } and {
                arithmetic_certificate {
                    negated_goal => to_integer(r2.end) <= (to_integer(r2.start) + to_integer(0));
                    premise 0: to_integer(r2.start) < to_integer(r2.end) => to_integer(r2.start) <
                        to_integer(r2.end);
                    add 0, 1 => (to_integer(r2.end) + to_integer(r2.start)) < (to_integer(r2.start) +
                        to_integer(0) + to_integer(r2.end));
                    conclusion 2;
                }
            }
        }
    }
    have r1.start == at(w2, r1.start) by {
        normalize();
    }
    have at(w2, r1.start) == at(z1, first->start) by {
        assumption();
    }
    have r1.start == at(z1, first->start) by {
        normalize() using {
            r1.start == at(w2, r1.start);
            at(w2, r1.start) == at(z1, first->start);
        };
    }
    have r1.end == at(w2, r1.end) by {
        normalize();
    }
    have at(w2, r1.end) == at(z1, first->end) by {
        assumption();
    }
    have r1.end == at(z1, first->end) by {
        normalize() using {
            r1.end == at(w2, r1.end);
            at(w2, r1.end) == at(z1, first->end);
        };
    }
    have s0.live == at(w2, s0.live) by {
        assumption();
    }
    have at(w2, s0.live) == 2 by {
        assumption();
    }
    have s0.live == 2 by {
        assumption();
    }
    have r2.start == at(w2, r2.start) by {
        assumption();
    }
    have at(w2, r2.start) == at(z2, second->start) by {
        normalize();
    }
    have r2.start == at(z2, second->start) by {
        normalize() using {
            r2.start == at(w2, r2.start);
            at(w2, r2.start) == at(z2, second->start);
        };
    }
    have r2.end == at(w2, r2.end) by {
        assumption();
    }
    have at(w2, r2.end) == at(z2, second->end) by {
        normalize();
    }
    have r2.end == at(z2, second->end) by {
        normalize() using {
            r2.end == at(w2, r2.end);
            at(w2, r2.end) == at(z2, second->end);
        };
    }
    have second->arena == arena by {
        assumption();
    }
    have second->arena->capacity == at(w2, second->arena->capacity) by {
        assumption();
    }
    have arena->capacity == second->arena->capacity by {
        assumption();
    }
    have at(w2, second->arena->capacity) == at(w2, arena->capacity) by {
        assumption();
    }
    have arena->capacity == at(w2, arena->capacity) by {
        assumption();
    }
    have s0.capacity == at(w2, s0.capacity) by {
        assumption();
    }
    have s0.capacity == arena->capacity by {
        normalize() using {
            s0.capacity == at(w2, s0.capacity);
            at(w2, s0.capacity) == at(w2, arena->capacity);
            arena->capacity == at(w2, arena->capacity);
        };
    }
    have forall (k: int32) { 0 <= k and k < arena->capacity and (k < at(z1, first->start) or at(z1, first->end) <= k) and (k < at(z2, second->start) or at(z2, second->end) <= k) implies arena->occupied[k] == 0 } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        extract(k < at(z1, first->start) or at(z1, first->end) <= k);
        extract(k < at(z2, second->start) or at(z2, second->end) <= k);
        have k < second->arena->capacity by {
            assumption();
        }
        have second->arena->occupied[k] == at(w2, second->arena->occupied[k]) by {
            instantiate(forall (j: int32) { 0 <= j and j < second->arena->capacity implies second->arena->occupied[j] == at(w2, second->arena->occupied[j]) }, k) using {
                0 <= k;
                k < second->arena->capacity;
            };
        }
        have at(w2, second->arena->occupied[k]) == at(w2, arena->occupied[k]) by {
            assumption();
        }
        have k < at(w2, arena->capacity) by {
            normalize() using {
                k < arena->capacity;
                arena->capacity == at(w2, arena->capacity);
            };
        }
        have at(w2, arena->occupied[k]) == 0 by {
            instantiate(forall (j: int32) { 0 <= j and j < at(w2, arena->capacity) and (j < at(z1, first->start) or at(z1, first->end) <= j) and (j < at(z2, second->start) or at(z2, second->end) <= j) implies at(w2, arena->occupied[j]) == 0 }, k) using {
                0 <= k;
                k < at(w2, arena->capacity);
                k < at(z1, first->start) or at(z1, first->end) <= k;
                k < at(z2, second->start) or at(z2, second->end) <= k;
            };
        }
        normalize() using {
            second->arena->occupied[k] == at(w2, second->arena->occupied[k]);
            at(w2, second->arena->occupied[k]) == at(w2, arena->occupied[k]);
            at(w2, arena->occupied[k]) == 0;
            second->arena == arena;
        };
    }
    have first->arena == arena by {
        assumption();
    }
    have s0.capacity == at(w2, s0.capacity) by {
        assumption();
    }
    have r1.end <= s0.capacity by {
        assumption();
    }
    have first->arena->data == second->arena->data by {
        assumption();
    }
    have at(w2, first->arena->data[(first->start + 0)]) == 11 by {
        assumption();
    }
    have first->start == at(w2, first->start) by {
        normalize();
    }
    have second->arena->data == at(w2, second->arena->data) by {
        assumption();
    }
    have at(w2, second->arena->data) == at(w2, first->arena->data) by {
        assumption();
    }
    have first->arena->data == at(w2, first->arena->data) by {
        assumption();
    }
    have &first->arena->data[first->start + 0] == at(w2, &first->arena->data[first->start + 0]) by {
        normalize() using {
            first->arena->data == at(w2, first->arena->data);
            first->start == at(w2, first->start);
        };
    }
    let { live: framed_live, capacity: framed_capacity } = unfold(s0);
    have at(region(22).entry, separate(memory(arena->occupied[0..arena->capacity]), memory(arena->data[0..arena->capacity]))) by assumption();
    have separate(memory(arena->occupied[0..arena->capacity]), memory(arena->data[0..arena->capacity])) by {
        have arena->occupied == at(region(22).entry, arena->occupied) by assumption();
        have arena->data == at(region(22).entry, arena->data) by assumption();
        rewrite(arena->occupied == at(region(22).entry, arena->occupied));
        rewrite(arena->data == at(region(22).entry, arena->data));
        assumption();
    }
    have separate(memory(*arena), memory(arena->data[0..arena->capacity])) by {
        have arena->data == at(region(22).entry, arena->data) by assumption();
        rewrite(arena->data == at(region(22).entry, arena->data));
        assumption();
    }
    have separate(memory(*arena), memory(arena->occupied[0..arena->capacity])) by {
        have arena->occupied == at(region(22).entry, arena->occupied) by assumption();
        rewrite(arena->occupied == at(region(22).entry, arena->occupied));
        assumption();
    }
    let { start: framed_start, end: framed_end } = unfold(r1);
    let r1 = fold(arena_region(first), { start: framed_start, end: framed_end });
    let s0 = fold(arena_state(arena), { live: framed_live, capacity: framed_capacity });
    have r1.start == first->start by {
        assumption();
    }
    have first->start < r1.end by {
        normalize() using { r1.start == first->start; r1.start < r1.end; };
    }
    have (r1.start as int32) <= ((first->start + 0) as int32) by {
        rewrite(first->start == r1.start);
        normalize();
    }
    have ((first->start + 0) as int32) < (r1.end as int32) by {
        rewrite(first->start == r1.start);
        normalize() using { r1.start < r1.end; };
    }
    have first->arena->data[(first->start + 0)] == at(w2, first->arena->data[(first->start + 0)]) by {
        transport(at(w2, first->arena->data[(first->start + 0)]) == at(w2, first->arena->data[(first->start + 0)]), first->arena->data[(first->start + 0)] == at(w2, first->arena->data[(first->start + 0)])) using {
            first->arena->data == at(w2, first->arena->data);
            first->start == at(w2, first->start);
            r1.start == first->start;
            first->start < r1.end;
            (r1.start as int32) <= ((first->start + 0) as int32);
            ((first->start + 0) as int32) < (r1.end as int32);
            &first->arena->data[first->start + 0] == at(w2, &first->arena->data[first->start + 0]);
        };
    }
    have first->arena->data[(first->start + 0)] == 11 by {
        normalize() using {
            first->arena->data[(first->start + 0)] == at(w2, first->arena->data[(first->start +
                0)]);
            at(w2, first->arena->data[(first->start + 0)]) == 11;
        };
    }
    have second->arena->data[(second->start + 0)] == 22 by {
        assumption();
    }
    mark m3;
    let { live: kept_live, capacity: kept_capacity } = unfold(s0);
    let { start: kept_start, end: kept_end } = unfold(r2);
    have ((second->start + 0) as int32) == (kept_start as int32) by {
        rewrite(second->start == kept_start);
        normalize();
    }
    have second->arena->data[kept_start] == 22 by {
        rewrite((kept_start as int32) == ((second->start + 0) as int32));
        assumption();
    }
    let kept = fold(preserved_cell((second->arena->data + kept_start)), { value: 22 });
    let s0 = fold(arena_state(arena), { live: kept_live, capacity: kept_capacity });
    step(arena_read, { r: r1, st: s0 });
    let { live: returned_live, capacity: returned_capacity } = unfold(s0);
    have at(region(23).entry, separate(memory(arena->occupied[0..arena->capacity]), memory(arena->data[0..arena->capacity]))) by assumption();
    have separate(memory(arena->occupied[0..arena->capacity]), memory(arena->data[0..arena->capacity])) by {
        have arena->occupied == at(region(23).entry, arena->occupied) by assumption();
        have arena->data == at(region(23).entry, arena->data) by assumption();
        rewrite(arena->occupied == at(region(23).entry, arena->occupied));
        rewrite(arena->data == at(region(23).entry, arena->data));
        assumption();
    }
    have separate(memory(*arena), memory(arena->data[0..arena->capacity])) by {
        have arena->data == at(region(23).entry, arena->data) by assumption();
        rewrite(arena->data == at(region(23).entry, arena->data));
        assumption();
    }
    have separate(memory(*arena), memory(arena->occupied[0..arena->capacity])) by {
        have arena->occupied == at(region(23).entry, arena->occupied) by assumption();
        rewrite(arena->occupied == at(region(23).entry, arena->occupied));
        assumption();
    }
    let {  } = unfold(kept);
    let s0 = fold(arena_state(arena), { live: returned_live, capacity: returned_capacity });
    have r1.start == at(m3, r1.start) by {
        assumption();
    }
    have at(m3, r1.start) == at(z1, first->start) by {
        assumption();
    }
    have r1.start == at(z1, first->start) by {
        normalize() using {
            r1.start == at(m3, r1.start);
            at(m3, r1.start) == at(z1, first->start);
        };
    }
    have r1.end == at(m3, r1.end) by {
        assumption();
    }
    have at(m3, r1.end) == at(z1, first->end) by {
        assumption();
    }
    have r1.end == at(z1, first->end) by {
        normalize() using {
            r1.end == at(m3, r1.end);
            at(m3, r1.end) == at(z1, first->end);
        };
    }
    have s0.live == at(m3, s0.live) by {
        assumption();
    }
    have at(m3, s0.live) == 2 by {
        assumption();
    }
    have s0.live == 2 by {
        normalize() using {
            s0.live == at(m3, s0.live);
            at(m3, s0.live) == 2;
        };
    }
    have kept_start == at(m3, kept_start) by {
        normalize();
    }
    have at(m3, kept_start) == at(z2, second->start) by {
        assumption();
    }
    have kept_start == at(z2, second->start) by {
        normalize() using {
            kept_start == at(m3, kept_start);
            at(m3, kept_start) == at(z2, second->start);
        };
    }
    have kept_end == at(m3, kept_end) by {
        normalize();
    }
    have at(m3, kept_end) == at(z2, second->end) by {
        assumption();
    }
    have kept_end == at(z2, second->end) by {
        normalize() using {
            kept_end == at(m3, kept_end);
            at(m3, kept_end) == at(z2, second->end);
        };
    }
    have first_value == 11 by {
        assumption();
    }
    have first->arena == arena by {
        normalize() using {
            first->arena == at(m3, first->arena);
            at(m3, first->arena) == arena;
        };
    }
    have first->arena->capacity == at(m3, first->arena->capacity) by {
        assumption();
    }
    have arena->capacity == first->arena->capacity by {
        assumption();
    }
    have at(m3, first->arena->capacity) == at(m3, arena->capacity) by {
        assumption();
    }
    have arena->capacity == at(m3, arena->capacity) by {
        normalize() using {
            arena->capacity == first->arena->capacity;
            first->arena->capacity == at(m3, first->arena->capacity);
            at(m3, first->arena->capacity) == at(m3, arena->capacity);
        };
    }
    have s0.capacity == at(m3, s0.capacity) by {
        assumption();
    }
    have s0.capacity == arena->capacity by {
        assumption();
    }
    have forall (k: int32) { 0 <= k and k < arena->capacity and (k < at(z1, first->start) or at(z1, first->end) <= k) and (k < at(z2, second->start) or at(z2, second->end) <= k) implies arena->occupied[k] == 0 } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        extract(k < at(z1, first->start) or at(z1, first->end) <= k);
        extract(k < at(z2, second->start) or at(z2, second->end) <= k);
        have k < first->arena->capacity by {
            assumption();
        }
        have first->arena->occupied[k] == at(m3, first->arena->occupied[k]) by {
            instantiate(forall (j: int32) { 0 <= j and j < first->arena->capacity implies first->arena->occupied[j] == at(m3, first->arena->occupied[j]) }, k) using {
                0 <= k;
                k < first->arena->capacity;
            };
        }
        have at(m3, first->arena->occupied[k]) == at(m3, arena->occupied[k]) by {
            normalize() using {
                at(m3, first->arena) == arena;
            };
        }
        have k < at(m3, arena->capacity) by {
            normalize() using {
                k < arena->capacity;
                arena->capacity == at(m3, arena->capacity);
            };
        }
        have at(m3, arena->occupied[k]) == 0 by {
            instantiate(forall (j: int32) { 0 <= j and j < at(m3, arena->capacity) and (j < at(z1, first->start) or at(z1, first->end) <= j) and (j < at(z2, second->start) or at(z2, second->end) <= j) implies at(m3, arena->occupied[j]) == 0 }, k) using {
                0 <= k;
                k < at(m3, arena->capacity);
                k < at(z1, first->start) or at(z1, first->end) <= k;
                k < at(z2, second->start) or at(z2, second->end) <= k;
            };
        }
        normalize() using {
            first->arena->occupied[k] == at(m3, first->arena->occupied[k]);
            at(m3, first->arena->occupied[k]) == at(m3, arena->occupied[k]);
            at(m3, arena->occupied[k]) == 0;
            first->arena == arena;
        };
    }
    have second->arena == arena by {
        assumption();
    }
    have second->start == at(m3, second->start) by {
        normalize();
    }
    have first->arena->data == at(m3, first->arena->data) by {
        assumption();
    }
    have second->arena->data == first->arena->data by {
        assumption();
    }
    have at(m3, first->arena->data) == at(m3, second->arena->data) by {
        assumption();
    }
    have second->arena->data == at(m3, second->arena->data) by {
        assumption();
    }
    have &second->arena->data[second->start + 0] == (at(m3, second->arena->data) + kept_start) by {
        normalize() using {
            second->arena->data == at(m3, second->arena->data);
            second->start == at(m3, second->start);
            at(m3, second->start) == kept_start;
        };
    }
    have second->arena->data[(second->start + 0)] == 22 by {
        rewrite(&second->arena->data[second->start + 0] == (at(m3, second->arena->data) + kept_start));
        assumption();
    }
    have (at(m3, second->arena->data) + at(m3, second->start)) == (second->arena->data + kept_start) by {
        normalize() using {
            second->arena->data == at(m3, second->arena->data);
            at(m3, second->start) == kept_start;
        };
    }
    have (at(m3, second->arena->data) + (at(m3, second->start) + 1)) == (second->arena->data + (kept_start + 1)) by {
        normalize() using {
            second->arena->data == at(m3, second->arena->data);
            at(m3, second->start) == kept_start;
        };
    }
    let r2 = fold(arena_region(second), { start: kept_start, end: kept_end });
    have r2.end <= s0.capacity by {
        assumption();
    }
    mark m4;
    step(arena_read, { r: r2, st: s0 });
    have r1.start == at(m4, r1.start) by {
        normalize();
    }
    have at(m4, r1.start) == at(z1, first->start) by {
        assumption();
    }
    have r1.start == at(z1, first->start) by {
        normalize() using {
            r1.start == at(m4, r1.start);
            at(m4, r1.start) == at(z1, first->start);
        };
    }
    have r1.end == at(m4, r1.end) by {
        normalize();
    }
    have at(m4, r1.end) == at(z1, first->end) by {
        assumption();
    }
    have r1.end == at(z1, first->end) by {
        normalize() using {
            r1.end == at(m4, r1.end);
            at(m4, r1.end) == at(z1, first->end);
        };
    }
    have s0.live == at(m4, s0.live) by {
        assumption();
    }
    have at(m4, s0.live) == 2 by {
        assumption();
    }
    have s0.live == 2 by {
        normalize() using {
            s0.live == at(m4, s0.live);
            at(m4, s0.live) == 2;
        };
    }
    have r2.start == at(m4, r2.start) by {
        assumption();
    }
    have at(m4, r2.start) == at(z2, second->start) by {
        assumption();
    }
    have r2.start == at(z2, second->start) by {
        normalize() using {
            r2.start == at(m4, r2.start);
            at(m4, r2.start) == at(z2, second->start);
        };
    }
    have r2.end == at(m4, r2.end) by {
        assumption();
    }
    have at(m4, r2.end) == at(z2, second->end) by {
        assumption();
    }
    have r2.end == at(z2, second->end) by {
        normalize() using {
            r2.end == at(m4, r2.end);
            at(m4, r2.end) == at(z2, second->end);
        };
    }
    have second_value == 22 by {
        assumption();
    }
    have first_value == 11 by {
        assumption();
    }
    step();
    have value == 33 by {
        assumption();
    }
    have second->arena == arena by {
        assumption();
    }
    have second->arena->capacity == at(m4, second->arena->capacity) by {
        assumption();
    }
    have arena->capacity == second->arena->capacity by {
        assumption();
    }
    have at(m4, second->arena->capacity) == at(m4, arena->capacity) by {
        normalize() using {
            at(m4, second->arena) == arena;
        };
    }
    have arena->capacity == at(m4, arena->capacity) by {
        normalize() using {
            arena->capacity == second->arena->capacity;
            second->arena->capacity == at(m4, second->arena->capacity);
            at(m4, second->arena->capacity) == at(m4, arena->capacity);
        };
    }
    have s0.capacity == at(m4, s0.capacity) by {
        assumption();
    }
    have s0.capacity == arena->capacity by {
        assumption();
    }
    have forall (k: int32) { 0 <= k and k < arena->capacity and (k < at(z1, first->start) or at(z1, first->end) <= k) and (k < at(z2, second->start) or at(z2, second->end) <= k) implies arena->occupied[k] == 0 } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        extract(k < at(z1, first->start) or at(z1, first->end) <= k);
        extract(k < at(z2, second->start) or at(z2, second->end) <= k);
        have k < second->arena->capacity by {
            normalize() using {
                k < arena->capacity;
                second->arena == arena;
            };
        }
        have second->arena->occupied[k] == at(m4, second->arena->occupied[k]) by {
            instantiate(forall (j: int32) { 0 <= j and j < second->arena->capacity implies second->arena->occupied[j] == at(m4, second->arena->occupied[j]) }, k) using {
                0 <= k;
                k < second->arena->capacity;
            };
        }
        have at(m4, second->arena->occupied[k]) == at(m4, arena->occupied[k]) by {
            normalize() using {
                at(m4, second->arena) == arena;
            };
        }
        have k < at(m4, arena->capacity) by {
            normalize() using {
                k < arena->capacity;
                arena->capacity == at(m4, arena->capacity);
            };
        }
        have at(m4, arena->occupied[k]) == 0 by {
            instantiate(forall (j: int32) { 0 <= j and j < at(m4, arena->capacity) and (j < at(z1, first->start) or at(z1, first->end) <= j) and (j < at(z2, second->start) or at(z2, second->end) <= j) implies at(m4, arena->occupied[j]) == 0 }, k) using {
                0 <= k;
                k < at(m4, arena->capacity);
                k < at(z1, first->start) or at(z1, first->end) <= k;
                k < at(z2, second->start) or at(z2, second->end) <= k;
            };
        }
        normalize() using {
            second->arena->occupied[k] == at(m4, second->arena->occupied[k]);
            at(m4, second->arena->occupied[k]) == at(m4, arena->occupied[k]);
            at(m4, arena->occupied[k]) == 0;
            second->arena == arena;
        };
    }
    have s0.live == 2 by {
        assumption();
    }
    have 1 <= s0.live by {
        arithmetic_certificate signed_int32 {
            premise 0: (at(region(25).entry, s0.live) as int32) == (at(region(25).entry, 2) as
                int32) => (at(region(25).entry, s0.live) as int32) == (at(region(25).entry, 2) as
                int32);
            less_equal_from_equal 0 reverse => to_integer((at(region(25).entry, 2) as int32)) <=
                to_integer((at(region(25).entry, s0.live) as int32));
            trivial => -1 <= 0;
            add 1, 2 => (to_integer((at(region(25).entry, 2) as int32)) + -1) <=
                (to_integer((at(region(25).entry, s0.live) as int32)) + 0);
            conclusion 3;
        }
    }
    have r2.end <= s0.capacity by {
        assumption();
    }
    have s0.capacity == arena->capacity by {
        assumption();
    }
    have r1.end <= s0.capacity by {
        have r1.end == at(m4, r1.end) by {
            normalize();
        }
        have s0.capacity == at(m4, s0.capacity) by {
            assumption();
        }
        have at(m4, r1.end) <= at(m4, s0.capacity) by {
            assumption();
        }
        assumption();
    }
    mark f2;
    let { after: g2 } = step(arena_free, { r: r2, st: s0 });
    have r1.start == at(f2, r1.start) by {
        normalize();
    }
    have at(f2, r1.start) == at(z1, first->start) by {
        assumption();
    }
    have r1.start == at(z1, first->start) by {
        normalize() using {
            r1.start == at(f2, r1.start);
            at(f2, r1.start) == at(z1, first->start);
        };
    }
    have r1.end == at(f2, r1.end) by {
        normalize();
    }
    have at(f2, r1.end) == at(z1, first->end) by {
        assumption();
    }
    have r1.end == at(z1, first->end) by {
        normalize() using {
            r1.end == at(f2, r1.end);
            at(f2, r1.end) == at(z1, first->end);
        };
    }
    have second->arena == arena by {
        assumption();
    }
    have second->arena->capacity == at(f2, second->arena->capacity) by {
        assumption();
    }
    have arena->capacity == second->arena->capacity by {
        assumption();
    }
    have at(f2, second->arena->capacity) == at(f2, arena->capacity) by {
        normalize() using {
            at(f2, second->arena) == arena;
        };
    }
    have arena->capacity == at(f2, arena->capacity) by {
        normalize() using {
            arena->capacity == second->arena->capacity;
            second->arena->capacity == at(f2, second->arena->capacity);
            at(f2, second->arena->capacity) == at(f2, arena->capacity);
        };
    }
    have second->start == at(f2, r2.start) by {
        assumption();
    }
    have at(f2, r2.start) == at(z2, second->start) by {
        assumption();
    }
    have second->start == at(z2, second->start) by {
        normalize() using {
            second->start == at(f2, r2.start);
            at(f2, r2.start) == at(z2, second->start);
        };
    }
    have second->end == at(f2, r2.end) by {
        assumption();
    }
    have at(f2, r2.end) == at(z2, second->end) by {
        assumption();
    }
    have second->end == at(z2, second->end) by {
        normalize() using {
            second->end == at(f2, r2.end);
            at(f2, r2.end) == at(z2, second->end);
        };
    }
    have forall (k: int32) { 0 <= k and k < arena->capacity and (k < at(z1, first->start) or at(z1, first->end) <= k) implies arena->occupied[k] == 0 } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        extract(k < at(z1, first->start) or at(z1, first->end) <= k);
        have k < second->start implies arena->occupied[k] == 0 by {
            intro();
            have second->arena->occupied[k] == at(f2, second->arena->occupied[k]) by {
                instantiate(forall (j: int32) { 0 <= j and j < second->start implies second->arena->occupied[j] == at(f2, second->arena->occupied[j]) }, k) using {
                    0 <= k;
                    k < second->start;
                };
            }
            have at(f2, second->arena->occupied[k]) == at(f2, arena->occupied[k]) by {
                normalize() using {
                    at(f2, second->arena) == arena;
                };
            }
            have k < at(f2, arena->capacity) by {
                normalize() using {
                    k < arena->capacity;
                    arena->capacity == at(f2, arena->capacity);
                };
            }
            have k < at(z2, second->start) by {
                assumption();
            }
            have k < at(z2, second->start) or at(z2, second->end) <= k by {
                assumption();
            }
            have at(f2, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) { 0 <= j and j < at(f2, arena->capacity) and (j < at(z1, first->start) or at(z1, first->end) <= j) and (j < at(z2, second->start) or at(z2, second->end) <= j) implies at(f2, arena->occupied[j]) == 0 }, k) using {
                    0 <= k;
                    k < at(f2, arena->capacity);
                    k < at(z1, first->start) or at(z1, first->end) <= k;
                    k < at(z2, second->start) or at(z2, second->end) <= k;
                };
            }
            normalize() using {
                second->arena->occupied[k] == at(f2, second->arena->occupied[k]);
                at(f2, second->arena->occupied[k]) == at(f2, arena->occupied[k]);
                at(f2, arena->occupied[k]) == 0;
                second->arena == arena;
            };
        }
        have second->start <= k and k < second->end implies arena->occupied[k] == 0 by {
            intro();
            extract(second->start <= k);
            extract(k < second->end);
            have arena->occupied[k] == 0 by {
                instantiate(forall (j: int32) { second->start <= j and j < second->end implies second->arena->occupied[j] == 0 }, k) using {
                    second->start <= k;
                    k < second->end;
                };
                normalize() using {
                    second->arena->occupied[k] == 0;
                    second->arena == arena;
                };
            }
            assumption();
        }
        have second->end <= k implies arena->occupied[k] == 0 by {
            intro();
            have k < second->arena->capacity by {
                normalize() using {
                    k < arena->capacity;
                    second->arena == arena;
                };
            }
            have second->arena->occupied[k] == at(f2, second->arena->occupied[k]) by {
                instantiate(forall (j: int32) { second->end <= j and j < second->arena->capacity implies second->arena->occupied[j] == at(f2, second->arena->occupied[j]) }, k) using {
                    second->end <= k;
                    k < second->arena->capacity;
                };
            }
            have at(f2, second->arena->occupied[k]) == at(f2, arena->occupied[k]) by {
                normalize() using {
                    at(f2, second->arena) == arena;
                };
            }
            have k < at(f2, arena->capacity) by {
                normalize() using {
                    k < arena->capacity;
                    arena->capacity == at(f2, arena->capacity);
                };
            }
            have at(z2, second->end) <= k by {
                normalize() using {
                    second->end <= k;
                    second->end == at(z2, second->end);
                };
            }
            have k < at(z2, second->start) or at(z2, second->end) <= k by {
                assumption();
            }
            have at(f2, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) { 0 <= j and j < at(f2, arena->capacity) and (j < at(z1, first->start) or at(z1, first->end) <= j) and (j < at(z2, second->start) or at(z2, second->end) <= j) implies at(f2, arena->occupied[j]) == 0 }, k) using {
                    0 <= k;
                    k < at(f2, arena->capacity);
                    k < at(z1, first->start) or at(z1, first->end) <= k;
                    k < at(z2, second->start) or at(z2, second->end) <= k;
                };
            }
            normalize() using {
                second->arena->occupied[k] == at(f2, second->arena->occupied[k]);
                at(f2, second->arena->occupied[k]) == at(f2, arena->occupied[k]);
                at(f2, arena->occupied[k]) == 0;
                second->arena == arena;
            };
        }
        if k < second->start {
            have k < second->start by {
                assumption();
            }
            extract(arena->occupied[k] == 0);
        } else {
            have second->start <= k by {
                assumption();
            }
            if k < second->end {
                have second->start <= k and k < second->end by {
                    assumption();
                }
                extract(arena->occupied[k] == 0);
            } else {
                have second->end <= k by {
                    assumption();
                }
                extract(arena->occupied[k] == 0);
            }
        }
    }
    have g2.live == 1 by {
        assumption();
    }
    have 1 <= g2.live by {
        arithmetic_certificate signed_int32 {
            premise 0: (at(region(26).entry, g2.live) as int32) == (at(region(26).entry, 1) as
                int32) => (at(region(26).entry, g2.live) as int32) == (at(region(26).entry, 1) as
                int32);
            less_equal_from_equal 0 reverse => to_integer((at(region(26).entry, 1) as int32)) <=
                to_integer((at(region(26).entry, g2.live) as int32));
            conclusion 1;
        }
    }
    have g2.capacity == at(f2, s0.capacity) by {
        assumption();
    }
    have at(f2, s0.capacity) == at(f2, arena->capacity) by {
        assumption();
    }
    have g2.capacity == arena->capacity by {
        assumption();
    }
    have r1.end <= g2.capacity by {
        have r1.end == at(f2, r1.end) by {
            normalize();
        }
        have at(f2, r1.end) <= at(f2, s0.capacity) by {
            assumption();
        }
        assumption();
    }
    have first->arena == arena by {
        assumption();
    }
    mark f3;
    let { after: g3 } = step(arena_free, { r: r1, st: g2 });
    have first->arena == arena by {
        normalize() using {
            first->arena == at(f3, first->arena);
            at(f3, first->arena) == arena;
        };
    }
    have first->arena->capacity == at(f3, first->arena->capacity) by {
        assumption();
    }
    have arena->capacity == first->arena->capacity by {
        assumption();
    }
    have at(f3, first->arena->capacity) == at(f3, arena->capacity) by {
        assumption();
    }
    have arena->capacity == at(f3, arena->capacity) by {
        normalize() using {
            arena->capacity == first->arena->capacity;
            first->arena->capacity == at(f3, first->arena->capacity);
            at(f3, first->arena->capacity) == at(f3, arena->capacity);
        };
    }
    have first->start == at(f3, r1.start) by {
        assumption();
    }
    have at(f3, r1.start) == at(z1, first->start) by {
        assumption();
    }
    have first->start == at(z1, first->start) by {
        normalize() using {
            first->start == at(f3, r1.start);
            at(f3, r1.start) == at(z1, first->start);
        };
    }
    have first->end == at(f3, r1.end) by {
        assumption();
    }
    have at(f3, r1.end) == at(z1, first->end) by {
        assumption();
    }
    have first->end == at(z1, first->end) by {
        normalize() using {
            first->end == at(f3, r1.end);
            at(f3, r1.end) == at(z1, first->end);
        };
    }
    have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == 0 } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        have k < first->start implies arena->occupied[k] == 0 by {
            intro();
            have first->arena->occupied[k] == at(f3, first->arena->occupied[k]) by {
                instantiate(forall (j: int32) { 0 <= j and j < first->start implies first->arena->occupied[j] == at(f3, first->arena->occupied[j]) }, k) using {
                    0 <= k;
                    k < first->start;
                };
            }
            have at(f3, first->arena->occupied[k]) == at(f3, arena->occupied[k]) by {
                normalize() using {
                    at(f3, first->arena) == arena;
                };
            }
            have k < at(f3, arena->capacity) by {
                assumption();
            }
            have k < at(z1, first->start) by {
                assumption();
            }
            have k < at(z1, first->start) or at(z1, first->end) <= k by {
                assumption();
            }
            have at(f3, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) { 0 <= j and j < at(f3, arena->capacity) and (j < at(z1, first->start) or at(z1, first->end) <= j) implies at(f3, arena->occupied[j]) == 0 }, k) using {
                    0 <= k;
                    k < at(f3, arena->capacity);
                    k < at(z1, first->start) or at(z1, first->end) <= k;
                };
            }
            normalize() using {
                first->arena->occupied[k] == at(f3, first->arena->occupied[k]);
                at(f3, first->arena->occupied[k]) == at(f3, arena->occupied[k]);
                at(f3, arena->occupied[k]) == 0;
                first->arena == arena;
            };
        }
        have first->start <= k and k < first->end implies arena->occupied[k] == 0 by {
            intro();
            extract(first->start <= k);
            extract(k < first->end);
            have arena->occupied[k] == 0 by {
                instantiate(forall (j: int32) { first->start <= j and j < first->end implies first->arena->occupied[j] == 0 }, k) using {
                    first->start <= k;
                    k < first->end;
                };
                normalize() using {
                    first->arena->occupied[k] == 0;
                    first->arena == arena;
                };
            }
            assumption();
        }
        have first->end <= k implies arena->occupied[k] == 0 by {
            intro();
            have k < first->arena->capacity by {
                assumption();
            }
            have first->arena->occupied[k] == at(f3, first->arena->occupied[k]) by {
                instantiate(forall (j: int32) { first->end <= j and j < first->arena->capacity implies first->arena->occupied[j] == at(f3, first->arena->occupied[j]) }, k) using {
                    first->end <= k;
                    k < first->arena->capacity;
                };
            }
            have at(f3, first->arena->occupied[k]) == at(f3, arena->occupied[k]) by {
                normalize() using {
                    at(f3, first->arena) == arena;
                };
            }
            have k < at(f3, arena->capacity) by {
                assumption();
            }
            have at(z1, first->end) <= k by {
                assumption();
            }
            have k < at(z1, first->start) or at(z1, first->end) <= k by {
                assumption();
            }
            have at(f3, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) { 0 <= j and j < at(f3, arena->capacity) and (j < at(z1, first->start) or at(z1, first->end) <= j) implies at(f3, arena->occupied[j]) == 0 }, k) using {
                    0 <= k;
                    k < at(f3, arena->capacity);
                    k < at(z1, first->start) or at(z1, first->end) <= k;
                };
            }
            normalize() using {
                first->arena->occupied[k] == at(f3, first->arena->occupied[k]);
                at(f3, first->arena->occupied[k]) == at(f3, arena->occupied[k]);
                at(f3, arena->occupied[k]) == 0;
                first->arena == arena;
            };
        }
        if k < first->start {
            have k < first->start by {
                assumption();
            }
            extract(arena->occupied[k] == 0);
        } else {
            have first->start <= k by {
                assumption();
            }
            if k < first->end {
                have first->start <= k and k < first->end by {
                    assumption();
                }
                extract(arena->occupied[k] == 0);
            } else {
                have first->end <= k by {
                    assumption();
                }
                extract(arena->occupied[k] == 0);
            }
        }
    }
    have g3.live == 0 by {
        assumption();
    }
    have g3.live < 2147483647 by {
        normalize() using {
            g3.live == 0;
        };
    }
    mark a3;
    let { outcome: o3 } = step(arena_alloc, { st: g3 });
    have allocated == 1 implies combined->arena == arena by {
        assumption();
    }
    have arena->capacity == at(a3, arena->capacity) by {
        assumption();
    }
    if at(region(28).entry, allocated) == at(region(28).entry, 0) {
        step();
        have o3.model == ArenaAllocOutcome::Failure() by {
            extract(o3.model == ArenaAllocOutcome::Failure());
        }
        have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == 0 } by {
            intro();
            intro();
            extract(0 <= k);
            extract(k < arena->capacity);
            have arena->occupied[k] == at(a3, arena->occupied[k]) by {
                instantiate(forall (j: int32) { allocated == 0 and 0 <= j and j < arena->capacity implies arena->occupied[j] == at(a3, arena->occupied[j]) }, k) using {
                    allocated == 0;
                    0 <= k;
                    k < arena->capacity;
                };
            }
            have k < at(a3, arena->capacity) by {
                assumption();
            }
            have at(a3, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) { 0 <= j and j < at(a3, arena->capacity) implies at(a3, arena->occupied[j]) == 0 }, k) using {
                    0 <= k;
                    k < at(a3, arena->capacity);
                };
            }
            normalize() using {
                arena->occupied[k] == at(a3, arena->occupied[k]);
                at(a3, arena->occupied[k]) == 0;
            };
        }
        step(arena_destroy, { st: g3 });
        unfold(o3);
        step();
        assumption();
        have result == 0 or result == 33 by {
            assumption();
        }
        assumption();
        assumption();
        assumption();
        assumption();
    } else {
        step();
        step();
        have allocated == 1 by {
            cases {
                allocated == 0 => {
                    contradiction(allocated == 0);
                }
                allocated == 1 => {
                    assumption();
                }
            }
        }
        have o3.model == ArenaAllocOutcome::Success(combined->start, combined->end) by {
            extract(o3.model == ArenaAllocOutcome::Success(combined->start, combined->end));
        }
        have 0 <= combined->start by {
            extract(0 <= combined->start);
        }
        have combined->start < combined->end by {
            extract(combined->start < combined->end);
        }
        have combined->end <= arena->capacity by {
            extract(combined->end <= arena->capacity);
        }
        have arena->capacity <= 536870911 by {
            assumption();
        }
        have combined->start < 536870911 by {
            arithmetic_certificate {
                premise 0: at(region(32).entry, combined->end) <= at(region(32).entry,
                    arena->capacity) => at(region(32).entry, combined->end) <= at(region(32).entry,
                    arena->capacity);
                premise 1: at(region(32).entry, arena->capacity) <= at(region(32).entry, 536870911)
                    => at(region(32).entry, arena->capacity) <= at(region(32).entry, 536870911);
                add 0, 1 => (at(region(32).entry, to_integer((combined->end as int32))) +
                    at(region(32).entry, to_integer((arena->capacity as int32)))) <=
                    (at(region(32).entry, to_integer((arena->capacity as int32))) +
                    at(region(32).entry, to_integer((536870911 as int32))));
                premise 2: at(region(32).entry, combined->start) < at(region(32).entry,
                    combined->end) => at(region(32).entry, combined->start) < at(region(32).entry,
                    combined->end);
                add 2, 3 => (at(region(32).entry, to_integer((combined->end as int32))) +
                    at(region(32).entry, to_integer((arena->capacity as int32))) +
                    at(region(32).entry, to_integer((combined->start as int32)))) <
                    (at(region(32).entry, to_integer((arena->capacity as int32))) +
                    at(region(32).entry, to_integer((536870911 as int32))) + at(region(32).entry,
                    to_integer((combined->end as int32))));
                conclusion 4;
            }
        }
        have g3.live == 1 by {
            assumption();
        }
        let { allocated: r3 } = unfold(o3);
        mark z3;
        have r3.start == at(z3, combined->start) by {
            normalize();
        }
        have r3.end == at(z3, combined->end) by {
            normalize();
        }
        have forall (k: int32) { 0 <= k and k < arena->capacity and (k < at(z3, combined->start) or at(z3, combined->end) <= k) implies arena->occupied[k] == 0 } by {
            intro();
            intro();
            extract(0 <= k);
            extract(k < arena->capacity);
            extract(k < at(z3, combined->start) or at(z3, combined->end) <= k);
            have k < at(a3, arena->capacity) by {
                assumption();
            }
            have at(a3, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) { 0 <= j and j < at(a3, arena->capacity) implies at(a3, arena->occupied[j]) == 0 }, k) using {
                    0 <= k;
                    k < at(a3, arena->capacity);
                };
            }
            cases {
                k < at(z3, combined->start) => {
                    have k < combined->start by {
                        assumption();
                    }
                    have arena->occupied[k] == at(a3, arena->occupied[k]) by {
                        instantiate(forall (j: int32) { allocated == 1 and 0 <= j and j < combined->start implies arena->occupied[j] == at(a3, arena->occupied[j]) }, k) using {
                            allocated == 1;
                            0 <= k;
                            k < combined->start;
                        };
                    }
                    rewrite(arena->occupied[k] == at(a3, arena->occupied[k]));
                    rewrite(at(a3, arena->occupied[k]) == 0);
                    normalize();
                }
                at(z3, combined->end) <= k => {
                    have combined->end <= k by {
                        assumption();
                    }
                    have arena->occupied[k] == at(a3, arena->occupied[k]) by {
                        instantiate(forall (j: int32) { allocated == 1 and combined->end <= j and j < arena->capacity implies arena->occupied[j] == at(a3, arena->occupied[j]) }, k) using {
                            allocated == 1;
                            combined->end <= k;
                            k < arena->capacity;
                        };
                    }
                    normalize() using {
                        arena->occupied[k] == at(a3, arena->occupied[k]);
                        at(a3, arena->occupied[k]) == 0;
                    };
                }
            }
        }
        have combined->arena == arena by {
            extract(combined->arena == arena);
        }
        have g3.capacity == arena->capacity by {
            assumption();
        }
        have 0 <= r3.start by {
            assumption();
        }
        have r3.start < 536870911 by {
            assumption();
        }
        have r3.start < 2147483643 by {
            arithmetic_certificate {
                premise 0: at(region(32).entry, combined->start) < at(region(32).entry, 536870911)
                    => at(region(32).entry, combined->start) < at(region(32).entry, 536870911);
                trivial => -1610612732 <= 0;
                add 0, 1 => (at(region(32).entry, to_integer((combined->start as int32))) +
                    -1610612732) < (at(region(32).entry, 536870911) + 0);
                conclusion 2;
            }
        }
        have r3.start <= 2147483643 by {
            arithmetic_certificate signed_int32 {
                premise 0: (at(region(32).entry, combined->start) as int32) < (at(region(32).entry,
                    536870911) as int32) => (at(region(32).entry, combined->start) as int32) <
                    (at(region(32).entry, 536870911) as int32);
                trivial => -1610612733 <= 0;
                add 0, 1 => (to_integer((at(region(32).entry, combined->start) as int32)) +
                    -1610612733) < (to_integer((at(region(32).entry, 536870911) as int32)) + 0);
                conclusion 2;
            }
        }
        have defined((r3.start + 4)) by {
            have (to_integer(r3.start) + to_integer(4)) >= -2147483648 by {
                arithmetic_certificate {
                    negated_goal => (to_integer(r3.start) + to_integer(4)) < -2147483648;
                    premise 0: 0 <= to_integer(r3.start) => 0 <= to_integer(r3.start);
                    add 0, 1 => (to_integer(r3.start) + to_integer(4) + 0) < (-2147483648 +
                        to_integer(r3.start));
                    conclusion 2;
                }
            }
            have (to_integer(r3.start) + to_integer(4)) <= 2147483647 by {
                arithmetic_certificate {
                    negated_goal => 2147483647 < (to_integer(r3.start) + to_integer(4));
                    premise 0: to_integer(r3.start) < 536870911 => to_integer(r3.start) < 536870911;
                    add 0, 1 => (2147483647 + 1 + (to_integer(r3.start) + 1)) <=
                        (to_integer(r3.start) + to_integer(4) + 536870911);
                    conclusion 2;
                }
            }
            assumption();
        }
        have at(z3, combined->start) == r3.start by {
            normalize() using {
                r3.start == at(z3, combined->start);
            };
        }
        have defined((at(z3, combined->start) + 4)) by {
            have defined(at(z3, combined->start)) by {
                transport(at(function.entry, viewable((combined as (uint8 *))[0..16])), defined(at(z3, combined->start))) using {
                    at(function.entry, viewable((combined as (uint8 *))[0..16]));
                };
            }
            arithmetic_certificate rules {
                premise 0: 0 <= at(z3, combined->start) => 0 <= at(z3, combined->start);
                premise 1: at(z3, combined->start) < 536870911 => at(z3, combined->start) <
                    536870911;
                premise 2: at(z3, combined->start) <= 2147483643 => at(z3, combined->start) <=
                    2147483643;
                premise 3: at(z3, combined->start) < 2147483643 => at(z3, combined->start) <
                    2147483643;
                premise 4: defined(at(z3, combined->start)) => defined(at(z3, combined->start));
                int32_defined bounds [0, 1, 2, 3, 4] => defined((at(z3, combined->start) + 4));
                conclusion 0;
            }
        }
        have to_integer((at(z3, combined->start) + 4)) == (to_integer(at(z3, combined->start)) + 4) by {
            have -2147483648 <= (to_integer(at(z3, combined->start)) + 4) by {
                assumption();
            }
            have (to_integer(at(z3, combined->start)) + 4) <= 2147483647 by {
                assumption();
            }
            have to_integer((at(z3, combined->start) + 4)) == (to_integer(at(z3, combined->start)) + 4) by {
                arithmetic_certificate rules {
                    premise 0: -2147483648 <= (to_integer(at(z3, combined->start)) + 4) =>
                        -2147483648 <= (to_integer(at(z3, combined->start)) + 4);
                    premise 1: (to_integer(at(z3, combined->start)) + 4) <= 2147483647 =>
                        (to_integer(at(z3, combined->start)) + 4) <= 2147483647;
                    integer_operation_identity bounds [0, 1] => to_integer((at(z3, combined->start)
                        + 4)) == (to_integer(at(z3, combined->start)) + 4);
                    conclusion 0;
                }
            }
            assumption();
        }
        have to_integer(at(z3, combined->end)) == to_integer((at(z3, combined->start) + 4)) by {
            rewrite(to_integer((at(z3, combined->start) + 4)) == (to_integer(at(z3, combined->start)) + 4));
            extract(to_integer(at(z3, combined->end)) == (to_integer(at(z3, combined->start)) + 4));
        }
        have to_integer(at(z3, combined->end)) == (to_integer(at(z3, combined->start)) + 4) by {
            normalize() using {
                to_integer(at(z3, combined->end)) == to_integer((at(z3, combined->start) + 4));
                to_integer((at(z3, combined->start) + 4)) == (to_integer(at(z3, combined->start)) +
                    4);
            };
        }
        have to_integer(r3.end) == (to_integer(r3.start) + 4) by {
            normalize() using {
                r3.start == at(z3, combined->start);
                r3.end == at(z3, combined->end);
                to_integer(at(z3, combined->end)) == (to_integer(at(z3, combined->start)) + 4);
            };
        }
        have r3.end <= g3.capacity by {
            assumption();
        }
        have r3.start <= 2147483644 by {
            arithmetic_certificate signed_int32 {
                premise 0: (at(region(32).entry, combined->start) as int32) < (at(region(32).entry,
                    536870911) as int32) => (at(region(32).entry, combined->start) as int32) <
                    (at(region(32).entry, 536870911) as int32);
                trivial => -1610612734 <= 0;
                add 0, 1 => (to_integer((at(region(32).entry, combined->start) as int32)) +
                    -1610612734) < (to_integer((at(region(32).entry, 536870911) as int32)) + 0);
                conclusion 2;
            }
        }
        have defined((r3.start + 3)) by {
            have (to_integer(r3.start) + to_integer(3)) >= -2147483648 by {
                arithmetic_certificate {
                    negated_goal => (to_integer(r3.start) + to_integer(3)) < -2147483648;
                    premise 0: 0 <= to_integer(r3.start) => 0 <= to_integer(r3.start);
                    add 0, 1 => (to_integer(r3.start) + to_integer(3) + 0) < (-2147483648 +
                        to_integer(r3.start));
                    conclusion 2;
                }
            }
            have (to_integer(r3.start) + to_integer(3)) <= 2147483647 by {
                arithmetic_certificate {
                    negated_goal => 2147483647 < (to_integer(r3.start) + to_integer(3));
                    premise 0: (let integer_value: Integer = to_integer((combined->start as int32))
                        + 4; integer_value) <= 2147483647 => (let integer_value: Integer =
                        to_integer((combined->start as int32)) + 4; integer_value) <= 2147483647;
                    add 0, 1 => (2147483647 + (let integer_value: Integer =
                        to_integer((combined->start as int32)) + 4; integer_value)) <
                        (to_integer(r3.start) + to_integer(3) + 2147483647);
                    conclusion 2;
                }
            }
            assumption();
        }
        have (to_integer(r3.start) + 3) < to_integer(r3.end) by {
            rewrite(to_integer(at(z3, combined->end)) == (to_integer(at(z3, combined->start)) + 4));
            normalize();
        }
        have value == 33 by {
            assumption();
        }
        mark w3;
        step(arena_write, { r: r3, st: g3 });
        have r3.start == at(w3, r3.start) by {
            assumption();
        }
        have defined((r3.start + 3)) by {
            assumption();
        }
        have combined->arena->data[(r3.start + 3)] == value by {
            assumption();
        }
        have combined->arena == arena by {
            assumption();
        }
        have combined->arena->capacity == at(w3, combined->arena->capacity) by {
            assumption();
        }
        have arena->capacity == combined->arena->capacity by {
            assumption();
        }
        have at(w3, combined->arena->capacity) == at(w3, arena->capacity) by {
            assumption();
        }
        have arena->capacity == at(w3, arena->capacity) by {
            assumption();
        }
        have g3.capacity == at(w3, g3.capacity) by {
            assumption();
        }
        have g3.capacity == arena->capacity by {
            assumption();
        }
        have forall (k: int32) { 0 <= k and k < arena->capacity and (k < at(z3, combined->start) or at(z3, combined->end) <= k) implies arena->occupied[k] == 0 } by {
            intro();
            intro();
            extract(0 <= k);
            extract(k < arena->capacity);
            extract(k < at(z3, combined->start) or at(z3, combined->end) <= k);
            have k < combined->arena->capacity by {
                assumption();
            }
            have combined->arena->occupied[k] == at(w3, combined->arena->occupied[k]) by {
                instantiate(forall (j: int32) { 0 <= j and j < combined->arena->capacity implies combined->arena->occupied[j] == at(w3, combined->arena->occupied[j]) }, k) using {
                    0 <= k;
                    k < combined->arena->capacity;
                };
            }
            have at(w3, combined->arena->occupied[k]) == at(w3, arena->occupied[k]) by {
                assumption();
            }
            have k < at(w3, arena->capacity) by {
                assumption();
            }
            have at(w3, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) { 0 <= j and j < at(w3, arena->capacity) and (j < at(z3, combined->start) or at(z3, combined->end) <= j) implies at(w3, arena->occupied[j]) == 0 }, k) using {
                    0 <= k;
                    k < at(w3, arena->capacity);
                    k < at(z3, combined->start) or at(z3, combined->end) <= k;
                };
            }
            normalize() using {
                combined->arena->occupied[k] == at(w3, combined->arena->occupied[k]);
                at(w3, combined->arena->occupied[k]) == at(w3, arena->occupied[k]);
                at(w3, arena->occupied[k]) == 0;
                combined->arena == arena;
            };
        }
        have g3.live == at(w3, g3.live) by {
            assumption();
        }
        have g3.live == 1 by {
            assumption();
        }
        have r3.start == at(w3, r3.start) by {
            assumption();
        }
        have r3.end == at(w3, r3.end) by {
            assumption();
        }
        have r3.start == at(z3, combined->start) by {
            assumption();
        }
        have r3.end == at(z3, combined->end) by {
            assumption();
        }
        have r3.end <= g3.capacity by {
            have r3.end <= at(w3, g3.capacity) by {
                assumption();
            }
            normalize() using {
                r3.end <= at(w3, g3.capacity);
                g3.capacity == at(w3, g3.capacity);
            };
        }
        have defined((r3.start + 3)) by {
            assumption();
        }
        have (to_integer(r3.start) + 3) < to_integer(r3.end) by {
            assumption();
        }
        have combined->arena->data[(r3.start + 3)] == 33 by {
            assumption();
        }
        mark m5;
        step(arena_read, { r: r3, st: g3 });
        have value == at(m5, combined->arena->data[(r3.start + 3)]) by {
            assumption();
        }
        have value == 33 by {
            assumption();
        }
        have combined->arena == arena by {
            assumption();
        }
        have combined->arena->capacity == at(m5, combined->arena->capacity) by {
            assumption();
        }
        have arena->capacity == combined->arena->capacity by {
            assumption();
        }
        have at(m5, combined->arena->capacity) == at(m5, arena->capacity) by {
            assumption();
        }
        have arena->capacity == at(m5, arena->capacity) by {
            assumption();
        }
        have g3.capacity == at(m5, g3.capacity) by {
            assumption();
        }
        have g3.capacity == arena->capacity by {
            assumption();
        }
        have forall (k: int32) { 0 <= k and k < arena->capacity and (k < at(z3, combined->start) or at(z3, combined->end) <= k) implies arena->occupied[k] == 0 } by {
            intro();
            intro();
            extract(0 <= k);
            extract(k < arena->capacity);
            extract(k < at(z3, combined->start) or at(z3, combined->end) <= k);
            have k < combined->arena->capacity by {
                assumption();
            }
            have combined->arena->occupied[k] == at(m5, combined->arena->occupied[k]) by {
                instantiate(forall (j: int32) { 0 <= j and j < combined->arena->capacity implies combined->arena->occupied[j] == at(m5, combined->arena->occupied[j]) }, k) using {
                    0 <= k;
                    k < combined->arena->capacity;
                };
            }
            have at(m5, combined->arena->occupied[k]) == at(m5, arena->occupied[k]) by {
                assumption();
            }
            have k < at(m5, arena->capacity) by {
                assumption();
            }
            have at(m5, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) { 0 <= j and j < at(m5, arena->capacity) and (j < at(z3, combined->start) or at(z3, combined->end) <= j) implies at(m5, arena->occupied[j]) == 0 }, k) using {
                    0 <= k;
                    k < at(m5, arena->capacity);
                    k < at(z3, combined->start) or at(z3, combined->end) <= k;
                };
            }
            normalize() using {
                combined->arena->occupied[k] == at(m5, combined->arena->occupied[k]);
                at(m5, combined->arena->occupied[k]) == at(m5, arena->occupied[k]);
                at(m5, arena->occupied[k]) == 0;
                combined->arena == arena;
            };
        }
        have g3.live == 1 by {
            assumption();
        }
        have 1 <= g3.live by {
            assumption();
        }
        have r3.start == at(z3, combined->start) by {
            assumption();
        }
        have r3.end == at(z3, combined->end) by {
            assumption();
        }
        have r3.end <= g3.capacity by {
            have r3.end == at(m5, r3.end) by {
                assumption();
            }
            have r3.end <= at(m5, g3.capacity) by {
                assumption();
            }
            normalize() using {
                r3.end <= at(m5, g3.capacity);
                g3.capacity == at(m5, g3.capacity);
            };
        }
        mark f4;
        let { after: g4 } = step(arena_free, { r: r3, st: g3 });
        have combined->arena == arena by {
            assumption();
        }
        have combined->arena->capacity == at(f4, combined->arena->capacity) by {
            assumption();
        }
        have arena->capacity == combined->arena->capacity by {
            assumption();
        }
        have at(f4, combined->arena->capacity) == at(f4, arena->capacity) by {
            assumption();
        }
        have arena->capacity == at(f4, arena->capacity) by {
            assumption();
        }
        have combined->start == at(z3, combined->start) by {
            assumption();
        }
        have combined->end == at(z3, combined->end) by {
            assumption();
        }
        have forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == 0 } by {
            intro();
            intro();
            extract(0 <= k);
            extract(k < arena->capacity);
            have k < combined->start implies arena->occupied[k] == 0 by {
                intro();
                have combined->arena->occupied[k] == at(f4, combined->arena->occupied[k]) by {
                    instantiate(forall (j: int32) { 0 <= j and j < combined->start implies combined->arena->occupied[j] == at(f4, combined->arena->occupied[j]) }, k) using {
                        0 <= k;
                        k < combined->start;
                    };
                }
                have at(f4, combined->arena->occupied[k]) == at(f4, arena->occupied[k]) by {
                    normalize() using {
                        at(f4, combined->arena) == arena;
                    };
                }
                have k < at(f4, arena->capacity) by {
                    normalize() using {
                        k < arena->capacity;
                        arena->capacity == at(f4, arena->capacity);
                    };
                }
                have k < at(z3, combined->start) by {
                    normalize() using {
                        k < combined->start;
                        combined->start == at(z3, combined->start);
                    };
                }
                have k < at(z3, combined->start) or at(z3, combined->end) <= k by {
                    assumption();
                }
                have at(f4, arena->occupied[k]) == 0 by {
                    instantiate(forall (j: int32) { 0 <= j and j < at(f4, arena->capacity) and (j < at(z3, combined->start) or at(z3, combined->end) <= j) implies at(f4, arena->occupied[j]) == 0 }, k) using {
                        0 <= k;
                        k < at(f4, arena->capacity);
                        k < at(z3, combined->start) or at(z3, combined->end) <= k;
                    };
                }
                normalize() using {
                    combined->arena->occupied[k] == at(f4, combined->arena->occupied[k]);
                    at(f4, combined->arena->occupied[k]) == at(f4, arena->occupied[k]);
                    at(f4, arena->occupied[k]) == 0;
                    combined->arena == arena;
                };
            }
            have combined->start <= k and k < combined->end implies arena->occupied[k] == 0 by {
                intro();
                extract(combined->start <= k);
                extract(k < combined->end);
                have arena->occupied[k] == 0 by {
                    instantiate(forall (j: int32) { combined->start <= j and j < combined->end implies combined->arena->occupied[j] == 0 }, k) using {
                        combined->start <= k;
                        k < combined->end;
                    };
                    normalize() using {
                        combined->arena->occupied[k] == 0;
                        combined->arena == arena;
                    };
                }
                assumption();
            }
            have combined->end <= k implies arena->occupied[k] == 0 by {
                intro();
                have k < combined->arena->capacity by {
                    normalize() using {
                        k < arena->capacity;
                        combined->arena == arena;
                    };
                }
                have combined->arena->occupied[k] == at(f4, combined->arena->occupied[k]) by {
                    instantiate(forall (j: int32) { combined->end <= j and j < combined->arena->capacity implies combined->arena->occupied[j] == at(f4, combined->arena->occupied[j]) }, k) using {
                        combined->end <= k;
                        k < combined->arena->capacity;
                    };
                }
                have at(f4, combined->arena->occupied[k]) == at(f4, arena->occupied[k]) by {
                    normalize() using {
                        at(f4, combined->arena) == arena;
                    };
                }
                have k < at(f4, arena->capacity) by {
                    normalize() using {
                        k < arena->capacity;
                        arena->capacity == at(f4, arena->capacity);
                    };
                }
                have at(z3, combined->end) <= k by {
                    normalize() using {
                        combined->end <= k;
                        combined->end == at(z3, combined->end);
                    };
                }
                have k < at(z3, combined->start) or at(z3, combined->end) <= k by {
                    assumption();
                }
                have at(f4, arena->occupied[k]) == 0 by {
                    instantiate(forall (j: int32) { 0 <= j and j < at(f4, arena->capacity) and (j < at(z3, combined->start) or at(z3, combined->end) <= j) implies at(f4, arena->occupied[j]) == 0 }, k) using {
                        0 <= k;
                        k < at(f4, arena->capacity);
                        k < at(z3, combined->start) or at(z3, combined->end) <= k;
                    };
                }
                normalize() using {
                    combined->arena->occupied[k] == at(f4, combined->arena->occupied[k]);
                    at(f4, combined->arena->occupied[k]) == at(f4, arena->occupied[k]);
                    at(f4, arena->occupied[k]) == 0;
                    combined->arena == arena;
                };
            }
            if k < combined->start {
                have k < combined->start by {
                    assumption();
                }
                extract(arena->occupied[k] == 0);
            } else {
                have combined->start <= k by {
                    assumption();
                }
                if k < combined->end {
                    have combined->start <= k and k < combined->end by {
                        assumption();
                    }
                    extract(arena->occupied[k] == 0);
                } else {
                    have combined->end <= k by {
                        assumption();
                    }
                    extract(arena->occupied[k] == 0);
                }
            }
        }
        step(arena_destroy, { st: g4 });
        step();
        assumption();
        have result == 0 or result == 33 by {
            assumption();
        }
        assumption();
        assumption();
        assumption();
        assumption();
    }
}

verifying "arena_reuse.c";

int32 arena_reuse(struct region* middle, struct region* reused) {
    consumes r: arena_region(middle);
    consumes st: arena_state(middle->arena);
    consumes *reused;
    requires r.start == 2;
    requires r.end == 4;
    requires st.capacity == 6;
    requires 1 <= st.live;
    requires forall (k: int32) {
        0 <= k and k < middle->arena->capacity implies middle->arena->occupied[k] == 1
    };
    produces *middle;
    produces after: arena_state(middle->arena);
    produces outcome: arena_alloc_result(reused);

    ensures result == 1 implies 2 <= reused->start and reused->end <= 4;
} by {
    step();
    let { after: after } = step(arena_free, { r: r, st: st });
    have middle->start == 2;
    have middle->end == 4;
    have after.live == old(st.live) - 1;
    have 0 < old(st.live);
    have old(st.live) - 1 < old(st.live);
    have forall (k: int32) {
        0 <= k and k < middle->arena->capacity implies
            (middle->arena->occupied[k] == 0 implies 2 <= k and k < 4)
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < middle->arena->capacity);
        intro();
        if k < 2 {
            have k < middle->start;
            instantiate(forall (j: int32) {
                0 <= j and j < middle->start implies
                    middle->arena->occupied[j] == old(middle->arena->occupied[j])
            }, k) using {
                0 <= k;
                k < middle->start;
            };
            have k < old(middle->arena->capacity);
            instantiate(forall (j: int32) {
                0 <= j and j < old(middle->arena->capacity) implies
                    old(middle->arena->occupied[j]) == 1
            }, k) using {
                0 <= k;
                k < old(middle->arena->capacity);
            };
            have middle->arena->occupied[k] == 1;
            have not (middle->arena->occupied[k] == 0);
            contradiction(middle->arena->occupied[k] == 0);
        } else {
            if k < 4 {
                have 2 <= k and k < 4;
                assumption();
            } else {
                have middle->end <= k;
                instantiate(forall (j: int32) {
                    middle->end <= j and j < middle->arena->capacity implies
                        middle->arena->occupied[j] == old(middle->arena->occupied[j])
                }, k) using {
                    middle->end <= k;
                    k < middle->arena->capacity;
                };
                have k < old(middle->arena->capacity);
                instantiate(forall (j: int32) {
                    0 <= j and j < old(middle->arena->capacity) implies
                        old(middle->arena->occupied[j]) == 1
                }, k) using {
                    0 <= k;
                    k < old(middle->arena->capacity);
                };
                have middle->arena->occupied[k] == 1;
                have not (middle->arena->occupied[k] == 0);
            contradiction(middle->arena->occupied[k] == 0);
            }
        }
    }
    mark allocating;
    let { outcome: outcome } = step(arena_alloc, { st: after });
    have middle->arena->capacity == at(allocating, middle->arena->capacity);
    have forall (k: int32) {
        allocated == 1 and reused->start <= k and k < reused->end implies 2 <= k and k < 4
    } by {
        intro();
        intro();
        extract(allocated == 1);
        extract(reused->start <= k);
        extract(k < reused->end);
        instantiate(forall (j: int32) {
            allocated == 1 and reused->start <= j and j < reused->end implies
                at(allocating, middle->arena->occupied[j]) == 0
        }, k) using {
            allocated == 1;
            reused->start <= k;
            k < reused->end;
        };
        have 0 <= reused->start;
        have 0 <= k;
        have reused->end <= middle->arena->capacity;
        have k < at(allocating, middle->arena->capacity) by {
            solve() using {
                k < reused->end;
                reused->end <= middle->arena->capacity;
                middle->arena->capacity == at(allocating, middle->arena->capacity);
            };
        }
        instantiate(forall (j: int32) {
            0 <= j and j < at(allocating, middle->arena->capacity) implies
                (at(allocating, middle->arena->occupied[j]) == 0 implies 2 <= j and j < 4)
        }, k) using {
            0 <= k;
            k < at(allocating, middle->arena->capacity);
            at(allocating, middle->arena->occupied[k]) == 0;
        };
        assumption();
    }
    have allocated == 1 implies 2 <= reused->start and reused->end <= 4 by {
        intro();
        have reused->start < reused->end;
        instantiate(forall (k: int32) {
            allocated == 1 and reused->start <= k and k < reused->end implies 2 <= k and k < 4
        }, reused->start) using {
            allocated == 1;
            reused->start <= reused->start;
            reused->start < reused->end;
        };
        have reused->start <= 4;
        have reused->end <= 4 by {
            if 4 < reused->end {
                instantiate(forall (k: int32) {
                    allocated == 1 and reused->start <= k and k < reused->end implies
                        2 <= k and k < 4
                }, 4) using {
                    allocated == 1;
                    reused->start <= 4;
                    4 < reused->end;
                };
                have not (4 < 4) by {
                    solve() using {};
                }
                contradiction(4 < 4);
            } else {
                solve() using {
                    not (4 < reused->end);
                };
            }
        }
        assumption();
    }
    step();
    solve();
}
