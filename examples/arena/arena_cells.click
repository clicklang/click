import click::integer;

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
    branch {
        step();
        let st = fold(arena_state(arena), { live: n, capacity: arena->capacity });
        let outcome = fold(arena_alloc_result(region), {
            model: ArenaAllocOutcome::Failure
        });
        have result == 0;
        have forall (k: int32) {
            result == 0 and 0 <= k and k < arena->capacity implies
                arena->occupied[k] == old(arena->occupied[k])
        } by {
            intro();
            intro();
            extract(0 <= k);
            extract(k < arena->capacity);
            transport(
                old(arena->occupied[k]) == old(arena->occupied[k]),
                arena->occupied[k] == old(arena->occupied[k])
            ) using {
                0 <= k;
                k < arena->capacity;
            };
        }
        assumption();
        have result == 0 or result == 1;
        assumption();
        have st.live == old(st.live) + result;
        assumption();
        have arena->capacity == old(arena->capacity);
        assumption();
        have arena->capacity <= 536870911;
        assumption();
        have st.capacity == arena->capacity;
        assumption();
        have result == 0 implies outcome.model == ArenaAllocOutcome::Failure;
        assumption();
        have result == 1 implies outcome.model ==
            ArenaAllocOutcome::Success(region->start, region->end) by solve();
        assumption();
        have result == 1 implies region->arena == arena;
        assumption();
        have result == 1 implies region->end == region->start + count;
        assumption();
        have result == 1 implies region->end <= arena->capacity;
        assumption();
        have result == 1 implies 0 <= region->start;
        assumption();
        have result == 1 implies region->start < region->end;
        assumption();
        have forall (k: int32) {
            result == 1 and region->start <= k and k < region->end implies
                arena->occupied[k] == 1
        } by {
            intro();
            intro();
            extract(result == 1);
            have not (result == 1);
            contradiction(result == 1);
        }
        assumption();
        have forall (k: int32) {
            result == 1 and 0 <= k and k < region->start implies
                arena->occupied[k] == old(arena->occupied[k])
        } by {
            intro();
            intro();
            extract(result == 1);
            have not (result == 1);
            contradiction(result == 1);
        }
        assumption();
        have forall (k: int32) {
            result == 1 and region->end <= k and k < arena->capacity implies
                arena->occupied[k] == old(arena->occupied[k])
        } by {
            intro();
            intro();
            extract(result == 1);
            have not (result == 1);
            contradiction(result == 1);
        }
        assumption();
        have forall (k: int32) {
            result == 1 and region->start <= k and k < region->end implies
                old(arena->occupied[k]) == 0
        } by {
            intro();
            intro();
            extract(result == 1);
            have not (result == 1);
            contradiction(result == 1);
        }
        assumption();
        assumption();
        assumption();
    } else {}
    branch {
        step();
        let st = fold(arena_state(arena), { live: n, capacity: arena->capacity });
        let outcome = fold(arena_alloc_result(region), {
            model: ArenaAllocOutcome::Failure
        });
        have result == 0;
        have forall (k: int32) {
            result == 0 and 0 <= k and k < arena->capacity implies
                arena->occupied[k] == old(arena->occupied[k])
        } by {
            intro();
            intro();
            extract(0 <= k);
            extract(k < arena->capacity);
            transport(
                old(arena->occupied[k]) == old(arena->occupied[k]),
                arena->occupied[k] == old(arena->occupied[k])
            ) using {
                0 <= k;
                k < arena->capacity;
            };
        }
        assumption();
        have result == 0 or result == 1;
        assumption();
        have st.live == old(st.live) + result;
        assumption();
        have arena->capacity == old(arena->capacity);
        assumption();
        have arena->capacity <= 536870911;
        assumption();
        have st.capacity == arena->capacity;
        assumption();
        have result == 0 implies outcome.model == ArenaAllocOutcome::Failure;
        assumption();
        have result == 1 implies outcome.model ==
            ArenaAllocOutcome::Success(region->start, region->end) by solve();
        assumption();
        have result == 1 implies region->arena == arena;
        assumption();
        have result == 1 implies region->end == region->start + count;
        assumption();
        have result == 1 implies region->end <= arena->capacity;
        assumption();
        have result == 1 implies 0 <= region->start;
        assumption();
        have result == 1 implies region->start < region->end;
        assumption();
        have forall (k: int32) {
            result == 1 and region->start <= k and k < region->end implies
                arena->occupied[k] == 1
        } by {
            intro();
            intro();
            extract(result == 1);
            have not (result == 1);
            contradiction(result == 1);
        }
        assumption();
        have forall (k: int32) {
            result == 1 and 0 <= k and k < region->start implies
                arena->occupied[k] == old(arena->occupied[k])
        } by {
            intro();
            intro();
            extract(result == 1);
            have not (result == 1);
            contradiction(result == 1);
        }
        assumption();
        have forall (k: int32) {
            result == 1 and region->end <= k and k < arena->capacity implies
                arena->occupied[k] == old(arena->occupied[k])
        } by {
            intro();
            intro();
            extract(result == 1);
            have not (result == 1);
            contradiction(result == 1);
        }
        assumption();
        have forall (k: int32) {
            result == 1 and region->start <= k and k < region->end implies
                old(arena->occupied[k]) == 0
        } by {
            intro();
            intro();
            extract(result == 1);
            have not (result == 1);
            contradiction(result == 1);
        }
        assumption();
        assumption();
        assumption();
    } else {}
    have 0 < count;
    have count <= arena->capacity;
    unfold(arena_cells(arena->data, arena->occupied, arena->capacity));
    step();
    step();
    have 0 <= arena->capacity;
    have forall (k: int32) {
        0 <= k and k < 0 implies arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < 0);
        have not (k < 0);
        contradiction(k < 0);
    }
    have forall (k: int32) {
        0 <= k and k < arena->capacity implies
            arena->occupied[k] == old(arena->occupied[k])
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        transport(
            old(arena->occupied[k]) == old(arena->occupied[k]),
            arena->occupied[k] == old(arena->occupied[k])
        ) using {
            0 <= k;
            k < arena->capacity;
        };
    }
    have viewable(arena->occupied[0..arena->capacity]);
    let run = fold(arena_scan(arena->data, arena->occupied, arena->capacity), {
        lo: 0, hi: 0
    });
    loop as find_first_free_run {
        decreases to_integer(arena->capacity) - to_integer(i);
        owns run: arena_scan(arena->data, arena->occupied, arena->capacity);
        invariant run.hi == i;
        invariant run.lo + run_length == i;
        invariant 0 <= run_length and run_length <= count;
        invariant forall (k: int32) {
            0 <= k and k < arena->capacity implies
                arena->occupied[k] == at(find_first_free_run.entry, arena->occupied[k])
        };

        invariant arena->data == old(arena->data);
        invariant arena->occupied == old(arena->occupied);

        initialize by solve();
        preserve by {
            mark iteration;
            let { lo: lo, hi: hi } = unfold(run);
            have hi == i;
            have lo + run_length == i;
            have lo <= i;
            have 0 <= i;
            have i + 1 <= arena->capacity;
            if arena->occupied[i] == 0 {
                have run_length + 1 <= count;
                branch {
                    step();
                } else {
                    contradiction(not (arena->occupied[i] == 0));
                }
                step();
                have forall (k: int32) {
                    lo <= k and k < i implies arena->occupied[k] == 0
                } by {
                    intro();
                    intro();
                    extract(lo <= k);
                    extract(k < i);
                    if k < at(iteration, i) {
                        have k < hi;
                        instantiate(forall (j: int32) {
                            lo <= j and j < hi implies arena->occupied[j] == 0
                        }, k) using {
                            lo <= k;
                            k < hi;
                        };
                        assumption();
                    } else {
                        have k <= at(iteration, i);
                        have k == at(iteration, i);
                        rewrite(k == at(iteration, i));
                        assumption();
                    }
                }
                have at(iteration, i) < at(iteration, i) + 1;
                have at(iteration, i) < i;
                have at(iteration, i) <= i;
                have lo <= i;
                have i <= arena->capacity;
                have run_length == at(iteration, run_length) + 1;
                have lo + at(iteration, run_length) == at(iteration, i);
                have lo + run_length == i;
                have 0 <= run_length and run_length <= count;
                have viewable(arena->occupied[0..arena->capacity]);
                let run = fold(arena_scan(arena->data, arena->occupied, arena->capacity), {
                    lo: lo, hi: i
                });
                have run.hi == i;
                have run.lo + run_length == i;
                have 0 <= at(iteration, i);
                have to_integer(at(iteration, i) + 1) == to_integer(at(iteration, i)) + 1;
                have 0 <= to_integer(arena->capacity) - to_integer(at(iteration, i) + 1);
                have forall (k: int32) {
                    0 <= k and k < arena->capacity implies
                        arena->occupied[k] == at(find_first_free_run.entry, arena->occupied[k])
                } by {
                    intro();
                    intro();
                    extract(0 <= k);
                    extract(k < arena->capacity);
                    have at(iteration, arena->occupied[k]) ==
                        at(find_first_free_run.entry, arena->occupied[k]) by {
                        instantiate(forall (j: int32) {
                            at(iteration, 0) <= at(iteration, j) and
                                at(iteration, j) < at(iteration, arena->capacity) implies
                                at(iteration, arena->occupied[j]) ==
                                    at(find_first_free_run.entry, arena->occupied[j])
                        }, k) using {
                            0 <= k;
                            k < arena->capacity;
                        };
                        assumption();
                    }
                    transport(
                        at(iteration, arena->occupied[k]) ==
                            at(find_first_free_run.entry, arena->occupied[k]),
                        arena->occupied[k] == at(find_first_free_run.entry, arena->occupied[k])
                    ) using {
                        at(iteration, arena->occupied[k]) ==
                            at(find_first_free_run.entry, arena->occupied[k]);
                        0 <= k;
                        k < arena->capacity;
                    };
                }
                close_invariants();
            } else {
                branch {
                    contradiction(arena->occupied[i] == 0);
                } else {
                    step();
                }
                step();
                have forall (k: int32) {
                    i <= k and k < i implies arena->occupied[k] == 0
                } by {
                    intro();
                    intro();
                    extract(i <= k);
                    extract(k < i);
                    have not (k < i);
                    contradiction(k < i);
                }
                have 0 <= i;
                have i <= arena->capacity;
                have viewable(arena->occupied[0..arena->capacity]);
                let run = fold(arena_scan(arena->data, arena->occupied, arena->capacity), {
                    lo: i, hi: i
                });
                have 0 <= at(iteration, i);
                have to_integer(at(iteration, i) + 1) == to_integer(at(iteration, i)) + 1;
                have 0 <= to_integer(arena->capacity) - to_integer(at(iteration, i) + 1);
                have forall (k: int32) {
                    0 <= k and k < arena->capacity implies
                        arena->occupied[k] == at(find_first_free_run.entry, arena->occupied[k])
                } by {
                    intro();
                    intro();
                    extract(0 <= k);
                    extract(k < arena->capacity);
                    have at(iteration, arena->occupied[k]) ==
                        at(find_first_free_run.entry, arena->occupied[k]) by {
                        instantiate(forall (j: int32) {
                            at(iteration, 0) <= at(iteration, j) and
                                at(iteration, j) < at(iteration, arena->capacity) implies
                                at(iteration, arena->occupied[j]) ==
                                    at(find_first_free_run.entry, arena->occupied[j])
                        }, k) using {
                            0 <= k;
                            k < arena->capacity;
                        };
                        assumption();
                    }
                    transport(
                        at(iteration, arena->occupied[k]) ==
                            at(find_first_free_run.entry, arena->occupied[k]),
                        arena->occupied[k] == at(find_first_free_run.entry, arena->occupied[k])
                    ) using {
                        at(iteration, arena->occupied[k]) ==
                            at(find_first_free_run.entry, arena->occupied[k]);
                        0 <= k;
                        k < arena->capacity;
                    };
                }
            }
        }
    }
    let { lo: run_lo, hi: run_hi } = unfold(run);
    have forall (k: int32) {
        0 <= k and k < arena->capacity implies
            arena->occupied[k] == old(arena->occupied[k])
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        instantiate(forall (j: int32) {
            0 <= j and j < arena->capacity implies
                arena->occupied[j] == at(find_first_free_run.entry, arena->occupied[j])
        }, k) using {
            0 <= k;
            k < arena->capacity;
        };
        instantiate(forall (j: int32) {
            at(find_first_free_run.entry, 0) <= at(find_first_free_run.entry, j) and
                at(find_first_free_run.entry, j) <
                    at(find_first_free_run.entry, arena->capacity) implies
                at(find_first_free_run.entry, arena->occupied[j]) == old(arena->occupied[j])
        }, k) using {
            0 <= k;
            k < arena->capacity;
        };
        rewrite(arena->occupied[k] == at(find_first_free_run.entry, arena->occupied[k]));
        assumption();
    }
    mark scanned;
    branch {
        fold(arena_cells(arena->data, arena->occupied, arena->capacity));
        step();
        let st = fold(arena_state(arena), { live: n, capacity: arena->capacity });
        let outcome = fold(arena_alloc_result(region), {
            model: ArenaAllocOutcome::Failure
        });
        have result == 0;
        have forall (k: int32) {
            result == 0 and 0 <= k and k < arena->capacity implies
                arena->occupied[k] == old(arena->occupied[k])
        } by {
            intro();
            intro();
            extract(0 <= k);
            extract(k < arena->capacity);
            instantiate(forall (j: int32) {
                at(scanned, 0) <= at(scanned, j) and at(scanned, j) < at(scanned, arena->capacity) implies
                    at(scanned, arena->occupied[j]) == old(arena->occupied[j])
            }, k) using {
                0 <= k;
                k < arena->capacity;
            };
            transport(
                at(scanned, arena->occupied[k]) == old(arena->occupied[k]),
                arena->occupied[k] == old(arena->occupied[k])
            ) using {
                at(scanned, arena->occupied[k]) == old(arena->occupied[k]);
                0 <= k;
                k < arena->capacity;
            };
        }
        assumption();
        have result == 0 or result == 1;
        assumption();
        have st.live == old(st.live) + result;
        assumption();
        have arena->capacity == old(arena->capacity);
        assumption();
        have arena->capacity <= 536870911;
        assumption();
        have st.capacity == arena->capacity;
        assumption();
        have result == 0 implies outcome.model == ArenaAllocOutcome::Failure;
        assumption();
        have result == 1 implies outcome.model ==
            ArenaAllocOutcome::Success(region->start, region->end) by solve();
        assumption();
        have result == 1 implies region->arena == arena;
        assumption();
        have result == 1 implies region->end == region->start + count;
        assumption();
        have result == 1 implies region->end <= arena->capacity;
        assumption();
        have result == 1 implies 0 <= region->start;
        assumption();
        have result == 1 implies region->start < region->end;
        assumption();
        have forall (k: int32) {
            result == 1 and region->start <= k and k < region->end implies
                arena->occupied[k] == 1
        } by {
            intro();
            intro();
            extract(result == 1);
            have not (result == 1);
            contradiction(result == 1);
        }
        assumption();
        have forall (k: int32) {
            result == 1 and 0 <= k and k < region->start implies
                arena->occupied[k] == old(arena->occupied[k])
        } by {
            intro();
            intro();
            extract(result == 1);
            have not (result == 1);
            contradiction(result == 1);
        }
        assumption();
        have forall (k: int32) {
            result == 1 and region->end <= k and k < arena->capacity implies
                arena->occupied[k] == old(arena->occupied[k])
        } by {
            intro();
            intro();
            extract(result == 1);
            have not (result == 1);
            contradiction(result == 1);
        }
        assumption();
        have forall (k: int32) {
            result == 1 and region->start <= k and k < region->end implies
                old(arena->occupied[k]) == 0
        } by {
            intro();
            intro();
            extract(result == 1);
            have not (result == 1);
            contradiction(result == 1);
        }
        assumption();
        assumption();
        assumption();
    } else {}
    have run_length == count;
    have count == run_length;
    have run_lo + count == i;
    have 0 <= count;
    have defined(run_lo + count);
    have count <= run_lo + count;
    have i == run_lo + count;
    have count <= i;
    have defined(i - count);
    step();
    have to_integer(i - count) == to_integer(i) - to_integer(count);
    have to_integer(start) == to_integer(run_lo);
    have start == run_lo;
    step();
    have end == i;
    have run_lo <= arena->capacity;
    have start < end;
    have forall (k: int32) {
        start <= k and k < end implies arena->occupied[k] == 0
    } by {
        rewrite(start == run_lo);
        rewrite(end == i);
        solve();
    }
    step();
    have i == start;
    have 0 <= start;
    have start <= end;
    have end <= arena->capacity;
    have forall (k: int32) {
        start <= k and k < start implies arena->occupied[k] == 1
    } by {
        intro();
        intro();
        extract(start <= k);
        extract(k < start);
        have not (k < start);
        contradiction(k < start);
    }
    have forall (k: int32) {
        0 <= k and k < arena->capacity implies
            arena->occupied[k] == old(arena->occupied[k])
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        instantiate(forall (j: int32) {
            at(scanned, 0) <= at(scanned, j) and at(scanned, j) < at(scanned, arena->capacity) implies
                at(scanned, arena->occupied[j]) == old(arena->occupied[j])
        }, k) using {
            0 <= k;
            k < arena->capacity;
        };
        transport(
            at(scanned, arena->occupied[k]) == old(arena->occupied[k]),
            arena->occupied[k] == old(arena->occupied[k])
        ) using {
            at(scanned, arena->occupied[k]) == old(arena->occupied[k]);
            0 <= k;
            k < arena->capacity;
        };
    }
    have forall (k: int32) {
        start <= k and k < end implies old(arena->occupied[k]) == 0
    } by {
        intro();
        intro();
        extract(start <= k);
        extract(k < end);
        have 0 <= k;
        have k < arena->capacity;
        instantiate(forall (j: int32) {
            start <= j and j < end implies arena->occupied[j] == 0
        }, k) using {
            start <= k;
            k < end;
        };
        instantiate(forall (j: int32) {
            0 <= j and j < arena->capacity implies
                arena->occupied[j] == old(arena->occupied[j])
        }, k) using {
            0 <= k;
            k < arena->capacity;
        };
        solve() using {
            arena->occupied[k] == 0;
            arena->occupied[k] == old(arena->occupied[k]);
        };
    }
    have viewable(arena->occupied[0..arena->capacity]);
    let w = fold(arena_window(
        arena->data,
        arena->occupied,
        arena->capacity,
        start,
        end
    ), {
        next: start
    });
    loop as mark_free_run {
        decreases to_integer(end) - to_integer(i);
        owns w: arena_window(
            arena->data,
            arena->occupied,
            arena->capacity,
            start,
            end
        );
        invariant w.next == i;
        invariant forall (k: int32) {
            0 <= k and k < start implies
                arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k])
        };
        invariant forall (k: int32) {
            end <= k and k < arena->capacity implies
                arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k])
        };

        invariant arena->data == old(arena->data);
        invariant arena->occupied == old(arena->occupied);

        initialize by solve();
        preserve by {
            let { next: m } = unfold(w);
            have m == i;
            have m <= i;
            have i < end;
            have end <= arena->capacity;
            have arena->occupied[i] == 0 by {
                instantiate(forall (k: int32) {
                    m <= k and k < end implies arena->occupied[k] == 0
                }, i) using {
                    m <= i;
                    i < end;
                };
                assumption();
            }
            take(arena->data[i..i + 1]);
            have start <= i;
            have 0 <= i;
            have i < arena->capacity;
            mark opened;
            step();
            transport(at(opened, arena->occupied) == old(arena->occupied),
                      arena->occupied == old(arena->occupied)) using {
                at(opened, arena->occupied) == old(arena->occupied);
                at(opened, separate(memory(*arena), memory(arena->occupied[0..arena->capacity])));
                0 <= at(opened, i);
                at(opened, i) < at(opened, arena->capacity);
            };
            transport(at(opened, arena->capacity) == old(arena->capacity),
                      arena->capacity == old(arena->capacity)) using {
                at(opened, arena->capacity) == old(arena->capacity);
                at(opened, separate(memory(*arena), memory(arena->occupied[0..arena->capacity])));
                0 <= at(opened, i);
                at(opened, i) < at(opened, arena->capacity);
            };
            transport(at(opened, arena->data) == old(arena->data),
                      arena->data == old(arena->data)) using {
                at(opened, arena->data) == old(arena->data);
                at(opened, separate(memory(*arena), memory(arena->occupied[0..arena->capacity])));
                0 <= at(opened, i);
                at(opened, i) < at(opened, arena->capacity);
            };
            have forall (k: int32) {
                at(opened, i) + 1 <= k and k < end implies
                    arena->occupied[k] == 0
            } by {
                intro();
                intro();
                extract(at(opened, i) + 1 <= k);
                extract(k < end);
                have at(opened, i) < k;
                have at(opened, i) <= k;
                have m <= k;
                have at(opened, arena->occupied[k]) == 0 by {
                    instantiate(forall (j: int32) {
                        at(opened, m) <= at(opened, j) and
                            at(opened, j) < at(opened, end) implies
                            at(opened, arena->occupied[j]) == at(opened, 0)
                    }, k) using {
                        m <= k;
                        k < end;
                    };
                    assumption();
                }
                have 0 <= k;
                have k < at(opened, arena->capacity);
                transport(
                    at(opened, arena->occupied[k]) == 0,
                    arena->occupied[k] == 0
                ) using {
                    at(opened, arena->occupied) == old(arena->occupied);
                    arena->occupied == old(arena->occupied);
                    at(opened, separate(memory(*arena), memory(arena->occupied[0..arena->capacity])));
                    at(opened, separate(memory(*arena), memory(arena->data[0..arena->capacity])));
                    at(opened, arena->occupied[k]) == 0;
                    at(opened, i) < k;
                    0 <= at(opened, i);
                    at(opened, i) < at(opened, arena->capacity);
                    0 <= k;
                    k < at(opened, arena->capacity);
                };
                assumption();
            }
            have forall (k: int32) {
                start <= k and k < at(opened, i) + 1 implies
                    arena->occupied[k] == 1
            } by {
                intro();
                intro();
                extract(start <= k);
                extract(k < at(opened, i) + 1);
                if k < at(opened, i) {
                    have k < m;
                    have at(opened, arena->occupied[k]) == 1 by {
                        instantiate(forall (j: int32) {
                            at(opened, start) <= at(opened, j) and
                                at(opened, j) < at(opened, m) implies
                                at(opened, arena->occupied[j]) == at(opened, 1)
                        }, k) using {
                            start <= k;
                            k < m;
                        };
                        assumption();
                    }
                    have 0 <= k;
                    transport(
                        at(opened, arena->occupied[k]) == 1,
                        arena->occupied[k] == 1
                    ) using {
                        at(opened, arena->occupied[k]) == 1;
                        k < at(opened, i);
                        0 <= k;
                        0 <= at(opened, i);
                        at(opened, i) < arena->capacity;
                    };
                } else {
                    have k <= at(opened, i);
                    have k == at(opened, i);
                    rewrite(k == at(opened, i));
                    normalize() using { arena->occupied == old(arena->occupied); };
                }
            }
            step();
            have forall (k: int32) {
                0 <= k and k < start implies
                    arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k])
            } by {
                intro();
                intro();
                extract(0 <= k);
                extract(k < start);
                have at(opened, arena->occupied[k]) ==
                    at(mark_free_run.entry, arena->occupied[k]) by {
                    instantiate(forall (j: int32) {
                        at(opened, 0) <= at(opened, j) and at(opened, j) < at(opened, start) implies
                            at(opened, arena->occupied[j]) ==
                                at(mark_free_run.entry, arena->occupied[j])
                    }, k) using {
                        0 <= k;
                        k < start;
                    };
                    assumption();
                }
                have k < at(opened, i);
                transport(
                    at(opened, arena->occupied[k]) ==
                        at(mark_free_run.entry, arena->occupied[k]),
                    arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k])
                ) using {
                    at(opened, arena->occupied[k]) ==
                        at(mark_free_run.entry, arena->occupied[k]);
                    k < at(opened, i);
                    0 <= k;
                    0 <= at(opened, i);
                    at(opened, i) < arena->capacity;
                };
            }
            have forall (k: int32) {
                end <= k and k < arena->capacity implies
                    arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k])
            } by {
                intro();
                intro();
                extract(end <= k);
                extract(k < arena->capacity);
                have k < at(opened, arena->capacity);
                have at(opened, arena->occupied[k]) ==
                    at(mark_free_run.entry, arena->occupied[k]) by {
                    instantiate(forall (j: int32) {
                        at(opened, end) <= at(opened, j) and
                            at(opened, j) < at(opened, arena->capacity) implies
                            at(opened, arena->occupied[j]) ==
                                at(mark_free_run.entry, arena->occupied[j])
                    }, k) using {
                        end <= k;
                        k < at(opened, arena->capacity);
                    };
                    assumption();
                }
                have at(opened, i) < k;
                have at(opened, i) <= k;
                have 0 <= k;
                transport(
                    at(opened, arena->occupied[k]) ==
                        at(mark_free_run.entry, arena->occupied[k]),
                    arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k])
                ) using {
                    at(opened, arena->occupied[k]) ==
                        at(mark_free_run.entry, arena->occupied[k]);
                    at(opened, i) < k;
                    0 <= at(opened, i);
                    at(opened, i) < arena->capacity;
                    0 <= k;
                    k < arena->capacity;
                };
            }
            have forall (k: int32) {
                i <= k and k < end implies arena->occupied[k] == 0
            } by {
                intro();
                intro();
                extract(i <= k);
                extract(k < end);
                have at(opened, i) + 1 <= k;
                instantiate(forall (j: int32) {
                    at(opened, i) + 1 <= j and j < end implies arena->occupied[j] == 0
                }, k) using {
                    at(opened, i) + 1 <= k;
                    k < end;
                };
                assumption();
            }
            have forall (k: int32) {
                start <= k and k < i implies arena->occupied[k] == 1
            } by {
                intro();
                intro();
                extract(start <= k);
                extract(k < i);
                have k < at(opened, i) + 1;
                instantiate(forall (j: int32) {
                    start <= j and j < at(opened, i) + 1 implies arena->occupied[j] == 1
                }, k) using {
                    start <= k;
                    k < at(opened, i) + 1;
                };
                assumption();
            }
            transport(
                at(opened, viewable(arena->occupied[0..arena->capacity])),
                viewable(arena->occupied[0..arena->capacity])
            ) using {
                at(opened, viewable(arena->occupied[0..arena->capacity]));
                at(opened, arena->occupied) == old(arena->occupied);
                arena->occupied == old(arena->occupied);
                at(opened, arena->capacity) == old(arena->capacity);
                arena->capacity == old(arena->capacity);
            };
            have forall (k: int32) {
                i <= k and k < end implies load_int32(old(arena->occupied) + k) == 0
            } by {
                rewrite(old(arena->occupied) == arena->occupied);
                assumption();
            }
            have forall (k: int32) {
                start <= k and k < i implies load_int32(old(arena->occupied) + k) == 1
            } by {
                rewrite(old(arena->occupied) == arena->occupied);
                assumption();
            }
            let w = fold(arena_window(
                old(arena->data),
                old(arena->occupied),
                old(arena->capacity),
                start,
                end
            ), {
                next: i
            });
            have to_integer(i) == to_integer(at(opened, i)) + 1;
            have 0 <= to_integer(end) - to_integer(i);
            have to_integer(end) - to_integer(i) < to_integer(end) - to_integer(at(opened, i));
            close_invariants() by {
                both { solve(); } and {
                    both { solve(); } and {
                        both { solve(); } and {
                            both { solve(); } and {
                                both { solve(); } and { solve(); }
                            }
                        }
                    }
                }
            }
        }
    }
    let { next: m } = unfold(w);
    have m <= end;
    have m == i;
    have not (m < end);
    have m == end;
    have forall (k: int32) {
        start <= k and k < end implies arena->occupied[k] == 1
    } by {
        intro();
        intro();
        extract(start <= k);
        extract(k < end);
        have k < m;
        instantiate(forall (j: int32) {
            start <= j and j < m implies arena->occupied[j] == 1
        }, k) using {
            start <= k;
            k < m;
        };
        assumption();
    }
    have forall (k: int32) {
        0 <= k and k < start implies arena->occupied[k] == old(arena->occupied[k])
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < start);
        instantiate(forall (j: int32) {
            0 <= j and j < start implies
                arena->occupied[j] == at(mark_free_run.entry, arena->occupied[j])
        }, k) using {
            0 <= k;
            k < start;
        };
        have k < end;
        have k < arena->capacity;
        instantiate(forall (j: int32) {
            at(mark_free_run.entry, 0) <= at(mark_free_run.entry, j) and at(mark_free_run.entry, j) < at(mark_free_run.entry, arena->capacity) implies
                at(mark_free_run.entry, arena->occupied[j]) == old(arena->occupied[j])
        }, k) using {
            0 <= k;
            k < arena->capacity;
        };
        solve() using {
            arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]);
            at(mark_free_run.entry, arena->occupied[k]) == old(arena->occupied[k]);
        };
    }
    have forall (k: int32) {
        end <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k])
    } by {
        intro();
        intro();
        extract(end <= k);
        extract(k < arena->capacity);
        instantiate(forall (j: int32) {
            end <= j and j < arena->capacity implies
                arena->occupied[j] == at(mark_free_run.entry, arena->occupied[j])
        }, k) using {
            end <= k;
            k < arena->capacity;
        };
        have 0 <= end;
        have 0 <= k;
        instantiate(forall (j: int32) {
            at(mark_free_run.entry, 0) <= at(mark_free_run.entry, j) and at(mark_free_run.entry, j) < at(mark_free_run.entry, arena->capacity) implies
                at(mark_free_run.entry, arena->occupied[j]) == old(arena->occupied[j])
        }, k) using {
            0 <= k;
            k < arena->capacity;
        };
        solve() using {
            arena->occupied[k] == at(mark_free_run.entry, arena->occupied[k]);
            at(mark_free_run.entry, arena->occupied[k]) == old(arena->occupied[k]);
        };
    }
    mark marked;
    step();
    step();
    step();
    have arena->live_regions == n;
    have n < 2147483647;
    have defined(n + 1);
    step();
    have region->start == start;
    have region->end == end;
    have forall (k: int32) {
        region->start <= k and k < region->end implies arena->occupied[k] == 1
    } by {
        intro();
        intro();
        extract(region->start <= k);
        extract(k < region->end);
        have start <= k;
        have k < end;
        have 0 <= k;
        have k < arena->capacity;
        instantiate(forall (j: int32) {
            at(marked, start) <= at(marked, j) and at(marked, j) < at(marked, end) implies
                at(marked, arena->occupied[j]) == at(marked, 1)
        }, k) using {
            start <= k;
            k < end;
        };
        transport(
            at(marked, arena->occupied[k]) == at(marked, 1),
            arena->occupied[k] == 1
        ) using {
            at(marked, arena->occupied[k]) == at(marked, 1);
            0 <= k;
            k < arena->capacity;
            separate(
                memory(*arena),
                memory(arena->occupied[0..arena->capacity])
            );
        };
    }
    have forall (k: int32) {
        0 <= k and k < region->start implies arena->occupied[k] == old(arena->occupied[k])
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < region->start);
        have k < start;
        have k < end;
        have k < arena->capacity;
        instantiate(forall (j: int32) {
            at(marked, 0) <= at(marked, j) and at(marked, j) < at(marked, start) implies
                at(marked, arena->occupied[j]) == old(arena->occupied[j])
        }, k) using {
            0 <= k;
            k < start;
        };
        transport(
            at(marked, arena->occupied[k]) == old(arena->occupied[k]),
            arena->occupied[k] == old(arena->occupied[k])
        ) using {
            at(marked, arena->occupied[k]) == old(arena->occupied[k]);
            0 <= k;
            k < arena->capacity;
            separate(
                memory(*arena),
                memory(arena->occupied[0..arena->capacity])
            );
        };
    }
    have forall (k: int32) {
        region->end <= k and k < arena->capacity implies arena->occupied[k] == old(arena->occupied[k])
    } by {
        intro();
        intro();
        extract(region->end <= k);
        extract(k < arena->capacity);
        have end <= k;
        have 0 <= end;
        have 0 <= k;
        instantiate(forall (j: int32) {
            at(marked, end) <= at(marked, j) and at(marked, j) < at(marked, arena->capacity) implies
                at(marked, arena->occupied[j]) == old(arena->occupied[j])
        }, k) using {
            end <= k;
            k < arena->capacity;
        };
        transport(
            at(marked, arena->occupied[k]) == old(arena->occupied[k]),
            arena->occupied[k] == old(arena->occupied[k])
        ) using {
            at(marked, arena->occupied[k]) == old(arena->occupied[k]);
            0 <= k;
            k < arena->capacity;
            separate(
                memory(*arena),
                memory(arena->occupied[0..arena->capacity])
            );
        };
    }
    mark stored;
    have forall (k: int32) {
        region->start <= k and k < region->end implies old(arena->occupied[k]) == 0
    } by {
        intro();
        intro();
        extract(region->start <= k);
        extract(k < region->end);
        have start <= k;
        have k < end;
        instantiate(forall (j: int32) {
            start <= j and j < end implies old(arena->occupied[j]) == 0
        }, k) using {
            start <= k;
            k < end;
        };
        assumption();
    }
    fold(arena_cells(arena->data, arena->occupied, arena->capacity));
    let allocated = fold(arena_region(region), { start: start, end: end });
    let st = fold(arena_state(arena), { live: n + 1, capacity: arena->capacity });
    let outcome = fold(arena_alloc_result(region), {
        model: ArenaAllocOutcome::Success(start, end)
    });
    step();
    have result == 1;
    have forall (k: int32) {
        result == 0 and 0 <= k and k < arena->capacity implies
            arena->occupied[k] == old(arena->occupied[k])
    } by {
        intro();
        intro();
        extract(result == 0);
        have not (result == 0);
        contradiction(result == 0);
    }
    assumption();
    have result == 0 or result == 1;
    assumption();
    have st.live == old(st.live) + result;
    assumption();
    have arena->capacity == old(arena->capacity);
    assumption();
    have arena->capacity <= 536870911;
    assumption();
    have st.capacity == arena->capacity;
    assumption();
    have result == 0 implies outcome.model == ArenaAllocOutcome::Failure;
    assumption();
    have result == 1 implies outcome.model ==
        ArenaAllocOutcome::Success(region->start, region->end) by solve();
    assumption();
    have result == 1 implies region->arena == arena;
    assumption();
    have result == 1 implies region->end == region->start + count;
    assumption();
    have result == 1 implies region->end <= arena->capacity;
    assumption();
    have result == 1 implies 0 <= region->start;
    assumption();
    have result == 1 implies region->start < region->end;
    assumption();
    have forall (k: int32) {
        result == 1 and region->start <= k and k < region->end implies
            arena->occupied[k] == 1
    } by {
        intro();
        intro();
        extract(region->start <= k);
        extract(k < region->end);
        instantiate(forall (j: int32) {
            at(stored, region->start) <= at(stored, j) and at(stored, j) < at(stored, region->end) implies
                at(stored, arena->occupied[j]) == at(stored, 1)
        }, k) using {
            region->start <= k;
            k < region->end;
        };
        transport(
            at(stored, arena->occupied[k]) == at(stored, 1),
            arena->occupied[k] == 1
        ) using {
            at(stored, arena->occupied[k]) == at(stored, 1);
        };
    }
    assumption();
    have forall (k: int32) {
        result == 1 and 0 <= k and k < region->start implies
            arena->occupied[k] == old(arena->occupied[k])
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < region->start);
        instantiate(forall (j: int32) {
            at(stored, 0) <= at(stored, j) and at(stored, j) < at(stored, region->start) implies
                at(stored, arena->occupied[j]) == old(arena->occupied[j])
        }, k) using {
            0 <= k;
            k < region->start;
        };
        transport(
            at(stored, arena->occupied[k]) == old(arena->occupied[k]),
            arena->occupied[k] == old(arena->occupied[k])
        ) using {
            at(stored, arena->occupied[k]) == old(arena->occupied[k]);
        };
    }
    assumption();
    have forall (k: int32) {
        result == 1 and region->end <= k and k < arena->capacity implies
            arena->occupied[k] == old(arena->occupied[k])
    } by {
        intro();
        intro();
        extract(region->end <= k);
        extract(k < arena->capacity);
        instantiate(forall (j: int32) {
            at(stored, region->end) <= at(stored, j) and at(stored, j) < at(stored, arena->capacity) implies
                at(stored, arena->occupied[j]) == old(arena->occupied[j])
        }, k) using {
            region->end <= k;
            k < arena->capacity;
        };
        transport(
            at(stored, arena->occupied[k]) == old(arena->occupied[k]),
            arena->occupied[k] == old(arena->occupied[k])
        ) using {
            at(stored, arena->occupied[k]) == old(arena->occupied[k]);
        };
    }
    assumption();
    have forall (k: int32) {
        result == 1 and region->start <= k and k < region->end implies
            old(arena->occupied[k]) == 0
    } by {
        intro();
        intro();
        extract(region->start <= k);
        extract(k < region->end);
        instantiate(forall (j: int32) {
            at(stored, region->start) <= at(stored, j) and at(stored, j) < at(stored, region->end) implies
                old(arena->occupied[j]) == 0
        }, k) using {
            region->start <= k;
            k < region->end;
        };
        assumption();
    }
    assumption();
    assumption();
    assumption();
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
    have viewable(region->arena->occupied[0..region->arena->capacity]);
    have separate(
        memory(*region),
        memory(region->arena->occupied[0..region->arena->capacity])
    ) by solve();
    mark unfolded;
    step();
    step();
    step();
    step();
    have e <= c;
    have arena->capacity == c;
    have e <= arena->capacity;
    have forall (k: int32) {
        region->start <= k and k < region->start implies arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(region->start <= k);
        extract(k < region->start);
        have not (k < region->start);
        contradiction(k < region->start);
    }
    have viewable(arena->occupied[0..arena->capacity]) by {
        transport(
            at(unfolded, viewable(region->arena->occupied[0..region->arena->capacity])),
            viewable(arena->occupied[0..arena->capacity])
        ) using {
            at(unfolded, viewable(region->arena->occupied[0..region->arena->capacity]));
        };
    }
    have forall (k: int32) {
        0 <= k and k < arena->capacity implies
            arena->occupied[k] == old(region->arena->occupied[k])
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        transport(
            old(region->arena->occupied[k]) == old(region->arena->occupied[k]),
            arena->occupied[k] == old(region->arena->occupied[k])
        ) using {
            0 <= k;
            k < arena->capacity;
        };
    }
    let w = fold(arena_clear_window(
        arena->data,
        arena->occupied,
        arena->capacity,
        region->start,
        region->end
    ), {
        next: region->start
    });
    loop as clear_occupied {
        decreases to_integer(region->end) - to_integer(i);
        owns w: arena_clear_window(arena->data, arena->occupied, arena->capacity, region->start, region->end);
        invariant w.next == i;
        invariant forall (k: int32) {
            0 <= k and k < region->start implies
                arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k])
        };
        invariant forall (k: int32) {
            region->end <= k and k < arena->capacity implies
                arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k])
        };
        invariant arena->data == at(clear_occupied.entry, arena->data);
        invariant arena->occupied == at(clear_occupied.entry, arena->occupied);
        invariant region->arena == old(region->arena);
        initialize by solve();
        preserve by {
            let { next: m } = unfold(w);
            have m == i;
            have 0 <= region->start;
            have region->start <= m;
            have region->start <= i;
            have 0 <= i;
            have region->end <= arena->capacity;
            have i < arena->capacity;
            mark opened;
            step();
            give(arena->data[i..i + 1]);
            step();
            have region->start <= at(opened, i) + 1;
            have forall (k: int32) {
                region->start <= k and k < at(opened, i) + 1 implies arena->occupied[k] == 0
            } by {
                intro();
                intro();
                extract(region->start <= k);
                extract(k < at(opened, i) + 1);
                if k < at(opened, i) {
                    have k < m;
                    have at(opened, arena->occupied[k]) == 0 by {
                        instantiate(forall (j: int32) {
                            at(opened, region->start) <= at(opened, j) and
                                at(opened, j) < at(opened, m) implies
                                at(opened, arena->occupied[j]) == at(opened, 0)
                        }, k) using {
                            region->start <= k;
                            k < m;
                        };
                        assumption();
                    }
                    have 0 <= k;
                    transport(at(opened, arena->occupied[k]) == 0, arena->occupied[k] == 0) using {
                        at(opened, arena->occupied[k]) == 0;
                        k < at(opened, i);
                        0 <= k;
                        0 <= at(opened, i);
                        at(opened, i) < arena->capacity;
                    };
                } else {
                    have to_integer(k) == to_integer(at(opened, i)) by solve() using {
                        k < at(opened, i) + 1;
                        not (k < at(opened, i));
                    };
                    rewrite(k == at(opened, i));
                    normalize();
                }
            }
            have forall (k: int32) {
                0 <= k and k < region->start implies
                    arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k])
            } by {
                intro();
                intro();
                extract(0 <= k);
                extract(k < region->start);
                have at(opened, arena->occupied[k]) ==
                    at(clear_occupied.entry, arena->occupied[k]) by {
                    instantiate(forall (j: int32) {
                        at(opened, 0) <= at(opened, j) and
                            at(opened, j) < at(opened, region->start) implies
                            at(opened, arena->occupied[j]) ==
                                at(clear_occupied.entry, arena->occupied[j])
                    }, k) using {
                        0 <= k;
                        k < region->start;
                    };
                    assumption();
                }
                have k < at(opened, i);
                transport(
                    at(opened, arena->occupied[k]) ==
                        at(clear_occupied.entry, arena->occupied[k]),
                    arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k])
                ) using {
                    at(opened, arena->occupied[k]) ==
                        at(clear_occupied.entry, arena->occupied[k]);
                    k < at(opened, i);
                    0 <= k;
                    0 <= at(opened, i);
                    at(opened, i) < arena->capacity;
                };
            }
            have forall (k: int32) {
                region->end <= k and k < arena->capacity implies
                    arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k])
            } by {
                intro();
                intro();
                extract(region->end <= k);
                extract(k < arena->capacity);
                have at(opened, arena->occupied[k]) ==
                    at(clear_occupied.entry, arena->occupied[k]) by {
                    instantiate(forall (j: int32) {
                        at(opened, region->end) <= at(opened, j) and
                            at(opened, j) < at(opened, arena->capacity) implies
                            at(opened, arena->occupied[j]) ==
                                at(clear_occupied.entry, arena->occupied[j])
                    }, k) using {
                        region->end <= k;
                        k < arena->capacity;
                    };
                    assumption();
                }
                have at(opened, i) < k;
                have at(opened, i) <= k;
                have 0 <= k;
                transport(
                    at(opened, arena->occupied[k]) ==
                        at(clear_occupied.entry, arena->occupied[k]),
                    arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k])
                ) using {
                    at(opened, arena->occupied[k]) ==
                        at(clear_occupied.entry, arena->occupied[k]);
                    at(opened, i) < k;
                    0 <= at(opened, i);
                    at(opened, i) < arena->capacity;
                    0 <= k;
                    k < arena->capacity;
                };
            }
            have forall (k: int32) {
                region->start <= k and k < i implies arena->occupied[k] == 0
            } by {
                intro();
                intro();
                extract(region->start <= k);
                extract(k < i);
                have k < at(opened, i) + 1;
                instantiate(forall (j: int32) {
                    region->start <= j and j < at(opened, i) + 1 implies arena->occupied[j] == 0
                }, k) using {
                    region->start <= k;
                    k < at(opened, i) + 1;
                };
                assumption();
            }
            let w = fold(arena_clear_window(arena->data, arena->occupied, arena->capacity, region->start, region->end), {
                next: i
            });
            have region->start <= region->end;
            have to_integer(i) == to_integer(at(opened, i)) + 1;
            have 0 <= to_integer(region->end) - to_integer(i);
            have to_integer(region->end) - to_integer(i) < to_integer(region->end) - to_integer(at(opened, i));
            close_invariants() by {
                both { solve(); } and {
                    both { solve(); } and {
                        both { solve(); } and {
                            both { solve(); } and {
                                both { solve(); } and {
                                    both { solve(); } and { solve(); }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    let { next: m } = unfold(w);
    have m <= region->end;
    have not (i < region->end);
    have not (m < region->end);
    have m == region->end;
    have region->start <= region->end;
    have 0 <= region->end;
    have region->end <= arena->capacity;
    have forall (k: int32) {
        region->start <= k and k < region->end implies arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(region->start <= k);
        extract(k < region->end);
        have k < m;
        instantiate(forall (j: int32) {
            region->start <= j and j < m implies arena->occupied[j] == 0
        }, k) using {
            region->start <= k;
            k < m;
        };
        assumption();
    }
    have forall (k: int32) {
        0 <= k and k < region->start implies
            arena->occupied[k] == old(region->arena->occupied[k])
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < region->start);
        instantiate(forall (j: int32) {
            0 <= j and j < region->start implies
                arena->occupied[j] == at(clear_occupied.entry, arena->occupied[j])
        }, k) using {
            0 <= k;
            k < region->start;
        };
        have k < region->end;
        have k < arena->capacity;
        instantiate(forall (j: int32) {
            at(clear_occupied.entry, 0) <= at(clear_occupied.entry, j) and at(clear_occupied.entry, j) < at(clear_occupied.entry, arena->capacity) implies
                at(clear_occupied.entry, arena->occupied[j]) == old(region->arena->occupied[j])
        }, k) using {
            0 <= k;
            k < arena->capacity;
        };
        solve() using {
            arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]);
            at(clear_occupied.entry, arena->occupied[k]) == old(region->arena->occupied[k]);
        };
    }
    have forall (k: int32) {
        region->end <= k and k < arena->capacity implies
            arena->occupied[k] == old(region->arena->occupied[k])
    } by {
        intro();
        intro();
        extract(region->end <= k);
        extract(k < arena->capacity);
        instantiate(forall (j: int32) {
            region->end <= j and j < arena->capacity implies
                arena->occupied[j] == at(clear_occupied.entry, arena->occupied[j])
        }, k) using {
            region->end <= k;
            k < arena->capacity;
        };
        have 0 <= k;
        instantiate(forall (j: int32) {
            at(clear_occupied.entry, 0) <= at(clear_occupied.entry, j) and at(clear_occupied.entry, j) < at(clear_occupied.entry, arena->capacity) implies
                at(clear_occupied.entry, arena->occupied[j]) == old(region->arena->occupied[j])
        }, k) using {
            0 <= k;
            k < arena->capacity;
        };
        solve() using {
            arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k]);
            at(clear_occupied.entry, arena->occupied[k]) == old(region->arena->occupied[k]);
        };
    }
    mark cleared;
    have 1 <= n;
    step();
    have forall (k: int32) {
        region->start <= k and k < region->end implies
            region->arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(region->start <= k);
        extract(k < region->end);
        have 0 <= k;
        have k < arena->capacity;
        instantiate(forall (j: int32) {
            at(cleared, region->start) <= at(cleared, j) and at(cleared, j) < at(cleared, region->end) implies
                at(cleared, arena->occupied[j]) == at(cleared, 0)
        }, k) using {
            region->start <= k;
            k < region->end;
        };
        transport(
            at(cleared, arena->occupied[k]) == at(cleared, 0),
            region->arena->occupied[k] == 0
        ) using {
            at(cleared, arena->occupied[k]) == at(cleared, 0);
            separate(
                memory(*arena),
                memory(arena->occupied[0..arena->capacity])
            );
            0 <= k;
            k < arena->capacity;
        };
    }
    have forall (k: int32) {
        0 <= k and k < region->start implies
            region->arena->occupied[k] == old(region->arena->occupied[k])
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < region->start);
        have k < region->end;
        have k < arena->capacity;
        instantiate(forall (j: int32) {
            at(cleared, 0) <= at(cleared, j) and at(cleared, j) < at(cleared, region->start) implies
                at(cleared, arena->occupied[j]) == old(region->arena->occupied[j])
        }, k) using {
            0 <= k;
            k < region->start;
        };
        transport(
            at(cleared, arena->occupied[k]) == old(region->arena->occupied[k]),
            region->arena->occupied[k] == old(region->arena->occupied[k])
        ) using {
            at(cleared, arena->occupied[k]) == old(region->arena->occupied[k]);
            separate(
                memory(*arena),
                memory(arena->occupied[0..arena->capacity])
            );
            0 <= k;
            k < arena->capacity;
        };
    }
    have forall (k: int32) {
        region->end <= k and k < arena->capacity implies
            region->arena->occupied[k] == old(region->arena->occupied[k])
    } by {
        intro();
        intro();
        extract(region->end <= k);
        extract(k < arena->capacity);
        have 0 <= k;
        instantiate(forall (j: int32) {
            at(cleared, region->end) <= at(cleared, j) and at(cleared, j) < at(cleared, arena->capacity) implies
                at(cleared, arena->occupied[j]) == old(region->arena->occupied[j])
        }, k) using {
            region->end <= k;
            k < arena->capacity;
        };
        transport(
            at(cleared, arena->occupied[k]) == old(region->arena->occupied[k]),
            region->arena->occupied[k] == old(region->arena->occupied[k])
        ) using {
            at(cleared, arena->occupied[k]) == old(region->arena->occupied[k]);
            separate(
                memory(*arena),
                memory(arena->occupied[0..arena->capacity])
            );
            0 <= k;
            k < arena->capacity;
        };
    }
    fold(arena_cells(arena->data, arena->occupied, arena->capacity));
    let after = fold(arena_state(arena), { live: n - 1, capacity: c });
    step_until(function.exit);
    solve();
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
    mark w;
    step_until(function.exit);
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
    let r = fold(arena_region(region), { start: s, end: e });
    let st = fold(arena_state(region->arena), { live: n, capacity: c });
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
    step_until(function.exit);
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
    branch {
        have o0.model == ArenaInitOutcome::Failure;
        unfold(o0);
        step_until(function.exit);
        solve();
    } else {}
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
    have o0.model == ArenaInitOutcome::Success(0, 8);
    let { state: s0 } = unfold(o0);
    have forall (k: int32) {
        0 <= k and k < arena->capacity implies arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        instantiate(forall (j: int32) {
            initialized == 1 and 0 <= j and j < arena->capacity implies
                arena->occupied[j] == 0
        }, k) using {
            initialized == 1;
            0 <= k;
            k < arena->capacity;
        };
        solve();
    }
    mark a1;
    let { outcome: o1 } = step(arena_alloc, { st: s0 });
    have arena->capacity == at(a1, arena->capacity);
    branch {
        have o1.model == ArenaAllocOutcome::Failure;
        have forall (k: int32) {
            0 <= k and k < arena->capacity implies arena->occupied[k] == 0
        } by {
            intro();
            intro();
            extract(0 <= k);
            extract(k < arena->capacity);
            have arena->occupied[k] == at(a1, arena->occupied[k]) by {
                instantiate(forall (j: int32) {
                    allocated == 0 and 0 <= j and j < arena->capacity implies
                        arena->occupied[j] == at(a1, arena->occupied[j])
                }, k) using {
                    allocated == 0;
                    0 <= k;
                    k < arena->capacity;
                };
                assumption();
            }
            have k < at(a1, arena->capacity);
            have at(a1, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) {
                    0 <= j and j < at(a1, arena->capacity) implies
                        at(a1, arena->occupied[j]) == 0
                }, k) using {
                    0 <= k;
                    k < at(a1, arena->capacity);
                };
                assumption();
            }
            solve();
        }
        step(arena_destroy, { st: s0 });
        unfold(o1);
        step_until(function.exit);
        solve();
    } else {}
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
    have o1.model == ArenaAllocOutcome::Success(first->start, first->end);
    have first->end <= arena->capacity;
    have first->arena == arena;
    let { allocated: r1 } = unfold(o1);
    mark z1;
    have r1.start == at(z1, first->start);
    have r1.end == at(z1, first->end);
    have forall (k: int32) {
        0 <= k and k < arena->capacity and (k < at(z1, first->start) or at(z1, first->end) <= k) implies
            arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        extract(k < at(z1, first->start) or at(z1, first->end) <= k);
        have k < at(a1, arena->capacity);
        have at(a1, arena->occupied[k]) == 0 by {
            instantiate(forall (j: int32) {
                0 <= j and j < at(a1, arena->capacity) implies
                    at(a1, arena->occupied[j]) == 0
            }, k) using {
                0 <= k;
                k < at(a1, arena->capacity);
            };
            assumption();
        }
        cases {
            k < at(z1, first->start) => {
                have k < first->start;
                have arena->occupied[k] == at(a1, arena->occupied[k]) by {
                    instantiate(forall (j: int32) {
                        allocated == 1 and 0 <= j and j < first->start implies
                            arena->occupied[j] == at(a1, arena->occupied[j])
                    }, k) using {
                        allocated == 1;
                        0 <= k;
                        k < first->start;
                    };
                    assumption();
                }
                solve();
            }
            at(z1, first->end) <= k => {
                have first->end <= k;
                have arena->occupied[k] == at(a1, arena->occupied[k]) by {
                    instantiate(forall (j: int32) {
                        allocated == 1 and first->end <= j and j < arena->capacity implies
                            arena->occupied[j] == at(a1, arena->occupied[j])
                    }, k) using {
                        allocated == 1;
                        first->end <= k;
                        k < arena->capacity;
                    };
                    assumption();
                }
                solve();
            }
        }
    }
    have at(a1, s0.live) == 0;
    have s0.live == 1;
    mark a2;
    let { outcome: o2 } = step(arena_alloc, { st: s0 });
    have arena->capacity == at(a2, arena->capacity);
    branch {
        have o2.model == ArenaAllocOutcome::Failure;
        have forall (k: int32) {
            0 <= k and k < arena->capacity and
                (k < at(z1, first->start) or at(z1, first->end) <= k) implies
                arena->occupied[k] == 0
        } by {
            intro();
            intro();
            extract(0 <= k);
            extract(k < arena->capacity);
            extract(k < at(z1, first->start) or at(z1, first->end) <= k);
            have arena->occupied[k] == at(a2, arena->occupied[k]) by {
                instantiate(forall (j: int32) {
                    allocated == 0 and 0 <= j and j < arena->capacity implies
                        arena->occupied[j] == at(a2, arena->occupied[j])
                }, k) using {
                    allocated == 0;
                    0 <= k;
                    k < arena->capacity;
                };
                assumption();
            }
            have k < at(a2, arena->capacity);
            have at(a2, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) {
                    0 <= j and j < at(a2, arena->capacity) and
                        (j < at(z1, first->start) or at(z1, first->end) <= j) implies
                        at(a2, arena->occupied[j]) == 0
                }, k) using {
                    0 <= k;
                    k < at(a2, arena->capacity);
                    k < at(z1, first->start) or at(z1, first->end) <= k;
                };
                assumption();
            }
            solve();
        }
        have at(a2, s0.live) == 1;
        have s0.live == 1;
        have r1.end <= at(z1, arena->capacity);
        have s0.capacity == arena->capacity;
        have r1.end <= s0.capacity;
        have 1 <= s0.live;
        have first->arena == arena;
        mark f1;
        let { after: g1 } = step(arena_free, { r: r1, st: s0 });
        have first->arena == arena;
        have first->arena->capacity == at(f1, first->arena->capacity);
        have arena->capacity == first->arena->capacity;
        have at(f1, first->arena->capacity) == at(f1, arena->capacity);
        have arena->capacity == at(f1, arena->capacity);
        have first->start == at(z1, first->start);
        have first->end == at(z1, first->end);
        have forall (k: int32) {
            0 <= k and k < arena->capacity implies arena->occupied[k] == 0
        } by {
            intro();
            intro();
            extract(0 <= k);
            extract(k < arena->capacity);
            have k < first->start implies arena->occupied[k] == 0 by {
                intro();
                have first->arena->occupied[k] == at(f1, first->arena->occupied[k]) by {
                    instantiate(forall (j: int32) {
                        0 <= j and j < first->start implies
                            first->arena->occupied[j] == at(f1, first->arena->occupied[j])
                    }, k) using {
                        0 <= k;
                        k < first->start;
                    };
                    assumption();
                }
                have at(f1, first->arena->occupied[k]) == at(f1, arena->occupied[k]);
                have k < at(f1, arena->capacity);
                have k < at(z1, first->start);
                have k < at(z1, first->start) or at(z1, first->end) <= k;
                have at(f1, arena->occupied[k]) == 0 by {
                    instantiate(forall (j: int32) {
                        0 <= j and j < at(f1, arena->capacity) and
                            (j < at(z1, first->start) or at(z1, first->end) <= j) implies
                            at(f1, arena->occupied[j]) == 0
                    }, k) using {
                        0 <= k;
                        k < at(f1, arena->capacity);
                        k < at(z1, first->start) or at(z1, first->end) <= k;
                    };
                    assumption();
                }
                solve() using {
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
                    instantiate(forall (j: int32) {
                        first->start <= j and j < first->end implies
                            first->arena->occupied[j] == 0
                    }, k) using {
                        first->start <= k;
                        k < first->end;
                    };
                    solve() using {
                        first->arena == arena;
                        first->arena->occupied[k] == 0;
                    };
                }
                assumption();
            }
            have first->end <= k implies arena->occupied[k] == 0 by {
                intro();
                have k < first->arena->capacity;
                have first->arena->occupied[k] == at(f1, first->arena->occupied[k]) by {
                    instantiate(forall (j: int32) {
                        first->end <= j and j < first->arena->capacity implies
                            first->arena->occupied[j] == at(f1, first->arena->occupied[j])
                    }, k) using {
                        first->end <= k;
                        k < first->arena->capacity;
                    };
                    assumption();
                }
                have at(f1, first->arena->occupied[k]) == at(f1, arena->occupied[k]);
                have k < at(f1, arena->capacity);
                have at(z1, first->end) <= k;
                have k < at(z1, first->start) or at(z1, first->end) <= k;
                have at(f1, arena->occupied[k]) == 0 by {
                    instantiate(forall (j: int32) {
                        0 <= j and j < at(f1, arena->capacity) and
                            (j < at(z1, first->start) or at(z1, first->end) <= j) implies
                            at(f1, arena->occupied[j]) == 0
                    }, k) using {
                        0 <= k;
                        k < at(f1, arena->capacity);
                        k < at(z1, first->start) or at(z1, first->end) <= k;
                    };
                    assumption();
                }
                solve() using {
                    first->arena == arena;
                    first->arena->occupied[k] == at(f1, first->arena->occupied[k]);
                    at(f1, first->arena->occupied[k]) == at(f1, arena->occupied[k]);
                    at(f1, arena->occupied[k]) == 0;
                };
            }
            if k < first->start {
                have k < first->start;
                extract(arena->occupied[k] == 0);
            } else {
                have first->start <= k;
                if k < first->end {
                    have first->start <= k and k < first->end;
                    extract(arena->occupied[k] == 0);
                } else {
                    have first->end <= k;
                    extract(arena->occupied[k] == 0);
                }
            }
        }
        step(arena_destroy, { st: g1 });
        unfold(o2);
        step_until(function.exit);
        solve();
    } else {}
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
    have o2.model == ArenaAllocOutcome::Success(second->start, second->end);
    have second->end <= arena->capacity;
    have second->arena == arena;
    let { allocated: r2 } = unfold(o2);
    have at(a2, s0.live) == 1;
    have s0.live == 2;
    mark z2;
    have r2.start == at(z2, second->start);
    have r2.end == at(z2, second->end);
    have forall (k: int32) {
        0 <= k and k < arena->capacity and
            (k < at(z1, first->start) or at(z1, first->end) <= k) and
            (k < at(z2, second->start) or at(z2, second->end) <= k) implies
            arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        extract(k < at(z1, first->start) or at(z1, first->end) <= k);
        extract(k < at(z2, second->start) or at(z2, second->end) <= k);
        have k < at(a2, arena->capacity);
        have at(a2, arena->occupied[k]) == 0 by {
            instantiate(forall (j: int32) {
                0 <= j and j < at(a2, arena->capacity) and
                    (j < at(z1, first->start) or at(z1, first->end) <= j) implies
                    at(a2, arena->occupied[j]) == 0
            }, k) using {
                0 <= k;
                k < at(a2, arena->capacity);
                k < at(z1, first->start) or at(z1, first->end) <= k;
            };
            assumption();
        }
        cases {
            k < at(z2, second->start) => {
                have k < second->start;
                have arena->occupied[k] == at(a2, arena->occupied[k]) by {
                    instantiate(forall (j: int32) {
                        allocated == 1 and 0 <= j and j < second->start implies
                            arena->occupied[j] == at(a2, arena->occupied[j])
                    }, k) using {
                        allocated == 1;
                        0 <= k;
                        k < second->start;
                    };
                    assumption();
                }
                solve();
            }
            at(z2, second->end) <= k => {
                have second->end <= k;
                have arena->occupied[k] == at(a2, arena->occupied[k]) by {
                    instantiate(forall (j: int32) {
                        allocated == 1 and second->end <= j and j < arena->capacity implies
                            arena->occupied[j] == at(a2, arena->occupied[j])
                    }, k) using {
                        allocated == 1;
                        second->end <= k;
                        k < arena->capacity;
                    };
                    assumption();
                }
                solve();
            }
        }
    }
    have first->arena == arena;
    have r1.start < r1.end;
    have r1.end <= at(z1, arena->capacity);
    have s0.capacity == arena->capacity;
    have arena->capacity == at(z1, arena->capacity);
    have r1.end <= s0.capacity;
    have first->arena == arena;
    mark w1;
    step(arena_write, { r: r1, st: s0 });
    have r1.start == at(w1, r1.start);
    have at(w1, r1.start) == at(z1, first->start);
    have r1.start == at(z1, first->start) by {
        normalize() using { r1.start == at(w1, r1.start); at(w1, r1.start) == at(z1, first->start); };
    }
    have r1.end == at(w1, r1.end);
    have at(w1, r1.end) == at(z1, first->end);
    have r1.end == at(z1, first->end) by {
        normalize() using { r1.end == at(w1, r1.end); at(w1, r1.end) == at(z1, first->end); };
    }
    have s0.live == at(w1, s0.live);
    have at(w1, s0.live) == 2;
    have s0.live == 2 by {
        normalize() using { s0.live == at(w1, s0.live); at(w1, s0.live) == 2; };
    }
    have r2.start == at(w1, r2.start);
    have at(w1, r2.start) == at(z2, second->start);
    have r2.start == at(z2, second->start) by {
        normalize() using { r2.start == at(w1, r2.start); at(w1, r2.start) == at(z2, second->start); };
    }
    have r2.end == at(w1, r2.end);
    have at(w1, r2.end) == at(z2, second->end);
    have r2.end == at(z2, second->end) by {
        normalize() using { r2.end == at(w1, r2.end); at(w1, r2.end) == at(z2, second->end); };
    }
    have first->arena == arena;
    have first->arena->capacity == at(w1, first->arena->capacity);
    have arena->capacity == first->arena->capacity;
    have at(w1, first->arena->capacity) == at(w1, arena->capacity);
    have arena->capacity == at(w1, arena->capacity);
    have forall (k: int32) {
        0 <= k and
            k < arena->capacity and
            (k < at(z1, first->start) or at(z1, first->end) <= k) and
            (k < at(z2, second->start) or at(z2, second->end) <= k) implies
            arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        extract(k < at(z1, first->start) or at(z1, first->end) <= k);
        extract(k < at(z2, second->start) or at(z2, second->end) <= k);
        have k < first->arena->capacity;
        have first->arena->occupied[k] == at(w1, first->arena->occupied[k]) by {
            instantiate(forall (j: int32) {
                0 <= j and j < first->arena->capacity implies
                    first->arena->occupied[j] == at(w1, first->arena->occupied[j])
            }, k) using {
                0 <= k;
                k < first->arena->capacity;
            };
            assumption();
        }
        have at(w1, first->arena->occupied[k]) == at(w1, arena->occupied[k]);
        have k < at(w1, arena->capacity);
        have at(w1, arena->occupied[k]) == 0 by {
            instantiate(forall (j: int32) {
                0 <= j and
                    j < at(w1, arena->capacity) and
                    (j < at(z1, first->start) or at(z1, first->end) <= j) and
                    (j < at(z2, second->start) or at(z2, second->end) <= j) implies
                    at(w1, arena->occupied[j]) == 0
            }, k) using {
                0 <= k;
                k < at(w1, arena->capacity);
                k < at(z1, first->start) or at(z1, first->end) <= k;
                k < at(z2, second->start) or at(z2, second->end) <= k;
            };
            assumption();
        }
        solve() using {
            first->arena->occupied[k] == at(w1, first->arena->occupied[k]);
            at(w1, first->arena->occupied[k]) == at(w1, arena->occupied[k]);
            at(w1, arena->occupied[k]) == 0;
            first->arena == arena;
        };
    }
    have second->arena == arena;
    have r2.start < r2.end;
    have r2.end <= at(z2, arena->capacity);
    have s0.capacity == at(w1, s0.capacity);
    have at(w1, s0.capacity) == at(w1, arena->capacity);
    have s0.capacity == arena->capacity;
    have arena->capacity == at(z2, arena->capacity);
    have r2.end <= s0.capacity;
    have first->arena->data == second->arena->data;
    mark w2;
    step(arena_write, { r: r2, st: s0 });
    have r1.start == at(w2, r1.start);
    have at(w2, r1.start) == at(z1, first->start);
    have r1.start == at(z1, first->start) by {
        normalize() using { r1.start == at(w2, r1.start); at(w2, r1.start) == at(z1, first->start); };
    }
    have r1.end == at(w2, r1.end);
    have at(w2, r1.end) == at(z1, first->end);
    have r1.end == at(z1, first->end) by {
        normalize() using { r1.end == at(w2, r1.end); at(w2, r1.end) == at(z1, first->end); };
    }
    have s0.live == at(w2, s0.live);
    have at(w2, s0.live) == 2;
    have s0.live == 2;
    have r2.start == at(w2, r2.start);
    have at(w2, r2.start) == at(z2, second->start);
    have r2.start == at(z2, second->start) by {
        normalize() using { r2.start == at(w2, r2.start); at(w2, r2.start) == at(z2, second->start); };
    }
    have r2.end == at(w2, r2.end);
    have at(w2, r2.end) == at(z2, second->end);
    have r2.end == at(z2, second->end) by {
        normalize() using { r2.end == at(w2, r2.end); at(w2, r2.end) == at(z2, second->end); };
    }
    have second->arena == arena;
    have second->arena->capacity == at(w2, second->arena->capacity);
    have arena->capacity == second->arena->capacity;
    have at(w2, second->arena->capacity) == at(w2, arena->capacity);
    have arena->capacity == at(w2, arena->capacity);
    have s0.capacity == at(w2, s0.capacity);
    have s0.capacity == arena->capacity by {
        solve() using {
            s0.capacity == at(w2, s0.capacity);
            at(w2, s0.capacity) == at(w2, arena->capacity);
            arena->capacity == at(w2, arena->capacity);
        };
    }
    have forall (k: int32) {
        0 <= k and
            k < arena->capacity and
            (k < at(z1, first->start) or at(z1, first->end) <= k) and
            (k < at(z2, second->start) or at(z2, second->end) <= k) implies
            arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        extract(k < at(z1, first->start) or at(z1, first->end) <= k);
        extract(k < at(z2, second->start) or at(z2, second->end) <= k);
        have k < second->arena->capacity;
        have second->arena->occupied[k] == at(w2, second->arena->occupied[k]) by {
            instantiate(forall (j: int32) {
                0 <= j and j < second->arena->capacity implies
                    second->arena->occupied[j] == at(w2, second->arena->occupied[j])
            }, k) using {
                0 <= k;
                k < second->arena->capacity;
            };
            assumption();
        }
        have at(w2, second->arena->occupied[k]) == at(w2, arena->occupied[k]);
        have k < at(w2, arena->capacity) by {
            solve() using {
                k < arena->capacity;
                arena->capacity == at(w2, arena->capacity);
            };
        }
        have at(w2, arena->occupied[k]) == 0 by {
            instantiate(forall (j: int32) {
                0 <= j and
                    j < at(w2, arena->capacity) and
                    (j < at(z1, first->start) or at(z1, first->end) <= j) and
                    (j < at(z2, second->start) or at(z2, second->end) <= j) implies
                    at(w2, arena->occupied[j]) == 0
            }, k) using {
                0 <= k;
                k < at(w2, arena->capacity);
                k < at(z1, first->start) or at(z1, first->end) <= k;
                k < at(z2, second->start) or at(z2, second->end) <= k;
            };
            assumption();
        }
        solve() using {
            second->arena->occupied[k] == at(w2, second->arena->occupied[k]);
            at(w2, second->arena->occupied[k]) == at(w2, arena->occupied[k]);
            at(w2, arena->occupied[k]) == 0;
            second->arena == arena;
        };
    }
    have first->arena == arena;
    have s0.capacity == at(w2, s0.capacity);
    have r1.end <= s0.capacity;
    have first->arena->data == second->arena->data;
    have at(w2, first->arena->data[first->start + 0]) == 11;
    have first->start == at(w2, first->start);
    have second->arena->data == at(w2, second->arena->data);
    have at(w2, second->arena->data) == at(w2, first->arena->data);
    have first->arena->data == at(w2, first->arena->data);
    have first->arena->data[first->start + 0] == at(w2, first->arena->data[first->start + 0]) by {
        transport(
            at(w2, first->arena->data[first->start + 0]) == at(w2, first->arena->data[first->start + 0]),
            first->arena->data[first->start + 0] == at(w2, first->arena->data[first->start + 0])
        ) using {
            first->arena->data == at(w2, first->arena->data);
            first->start == at(w2, first->start);
        };
    }
    have first->arena->data[first->start + 0] == 11 by {
        normalize() using {
            first->arena->data[first->start + 0] == at(w2, first->arena->data[first->start + 0]);
            at(w2, first->arena->data[first->start + 0]) == 11;
        };
    }
    have second->arena->data[second->start + 0] == 22;
    mark m3;
    step(arena_read, { r: r1, st: s0 });
    have r1.start == at(m3, r1.start);
    have at(m3, r1.start) == at(z1, first->start);
    have r1.start == at(z1, first->start) by {
        normalize() using { r1.start == at(m3, r1.start); at(m3, r1.start) == at(z1, first->start); };
    }
    have r1.end == at(m3, r1.end);
    have at(m3, r1.end) == at(z1, first->end);
    have r1.end == at(z1, first->end) by {
        normalize() using { r1.end == at(m3, r1.end); at(m3, r1.end) == at(z1, first->end); };
    }
    have s0.live == at(m3, s0.live);
    have at(m3, s0.live) == 2;
    have s0.live == 2 by {
        normalize() using { s0.live == at(m3, s0.live); at(m3, s0.live) == 2; };
    }
    have r2.start == at(m3, r2.start);
    have at(m3, r2.start) == at(z2, second->start);
    have r2.start == at(z2, second->start) by {
        normalize() using { r2.start == at(m3, r2.start); at(m3, r2.start) == at(z2, second->start); };
    }
    have r2.end == at(m3, r2.end);
    have at(m3, r2.end) == at(z2, second->end);
    have r2.end == at(z2, second->end) by {
        normalize() using { r2.end == at(m3, r2.end); at(m3, r2.end) == at(z2, second->end); };
    }
    have first_value == 11;
    have first->arena == arena by {
        solve() using {
            first->arena == at(m3, first->arena);
            at(m3, first->arena) == arena;
        };
    }
    have first->arena->capacity == at(m3, first->arena->capacity);
    have arena->capacity == first->arena->capacity;
    have at(m3, first->arena->capacity) == at(m3, arena->capacity);
    have arena->capacity == at(m3, arena->capacity) by {
        solve() using {
            arena->capacity == first->arena->capacity;
            first->arena->capacity == at(m3, first->arena->capacity);
            at(m3, first->arena->capacity) == at(m3, arena->capacity);
        };
    }
    have s0.capacity == at(m3, s0.capacity);
    have s0.capacity == arena->capacity;
    have forall (k: int32) {
        0 <= k and
            k < arena->capacity and
            (k < at(z1, first->start) or at(z1, first->end) <= k) and
            (k < at(z2, second->start) or at(z2, second->end) <= k) implies
            arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        extract(k < at(z1, first->start) or at(z1, first->end) <= k);
        extract(k < at(z2, second->start) or at(z2, second->end) <= k);
        have k < first->arena->capacity;
        have first->arena->occupied[k] == at(m3, first->arena->occupied[k]) by {
            instantiate(forall (j: int32) {
                0 <= j and j < first->arena->capacity implies
                    first->arena->occupied[j] == at(m3, first->arena->occupied[j])
            }, k) using {
                0 <= k;
                k < first->arena->capacity;
            };
            assumption();
        }
        have at(m3, first->arena->occupied[k]) == at(m3, arena->occupied[k]) by {
            solve() using {
                at(m3, first->arena) == arena;
            };
        }
        have k < at(m3, arena->capacity) by {
            solve() using {
                k < arena->capacity;
                arena->capacity == at(m3, arena->capacity);
            };
        }
        have at(m3, arena->occupied[k]) == 0 by {
            instantiate(forall (j: int32) {
                0 <= j and
                    j < at(m3, arena->capacity) and
                    (j < at(z1, first->start) or at(z1, first->end) <= j) and
                    (j < at(z2, second->start) or at(z2, second->end) <= j) implies
                    at(m3, arena->occupied[j]) == 0
            }, k) using {
                0 <= k;
                k < at(m3, arena->capacity);
                k < at(z1, first->start) or at(z1, first->end) <= k;
                k < at(z2, second->start) or at(z2, second->end) <= k;
            };
            assumption();
        }
        solve() using {
            first->arena->occupied[k] == at(m3, first->arena->occupied[k]);
            at(m3, first->arena->occupied[k]) == at(m3, arena->occupied[k]);
            at(m3, arena->occupied[k]) == 0;
            first->arena == arena;
        };
    }
    have second->arena == arena;
    have second->start == at(m3, second->start);
    have first->arena->data == at(m3, first->arena->data);
    have second->arena->data == first->arena->data;
    have at(m3, first->arena->data) == at(m3, second->arena->data);
    have second->arena->data == at(m3, second->arena->data);
    have second->arena->data[second->start + 0] == at(m3, second->arena->data[second->start + 0]) by {
        transport(
            at(m3, second->arena->data[second->start + 0]) == at(m3, second->arena->data[second->start + 0]),
            second->arena->data[second->start + 0] == at(m3, second->arena->data[second->start + 0])
        ) using {
            second->arena->data == at(m3, second->arena->data);
            second->start == at(m3, second->start);
        };
    }
    have second->arena->data[second->start + 0] == 22 by {
        normalize() using {
            second->arena->data[second->start + 0] == at(m3, second->arena->data[second->start + 0]);
            at(m3, second->arena->data[second->start + 0]) == 22;
        };
    }
    have r2.end <= s0.capacity;
    mark m4;
    step(arena_read, { r: r2, st: s0 });
    have r1.start == at(m4, r1.start);
    have at(m4, r1.start) == at(z1, first->start);
    have r1.start == at(z1, first->start) by {
        normalize() using { r1.start == at(m4, r1.start); at(m4, r1.start) == at(z1, first->start); };
    }
    have r1.end == at(m4, r1.end);
    have at(m4, r1.end) == at(z1, first->end);
    have r1.end == at(z1, first->end) by {
        normalize() using { r1.end == at(m4, r1.end); at(m4, r1.end) == at(z1, first->end); };
    }
    have s0.live == at(m4, s0.live);
    have at(m4, s0.live) == 2;
    have s0.live == 2 by {
        normalize() using { s0.live == at(m4, s0.live); at(m4, s0.live) == 2; };
    }
    have r2.start == at(m4, r2.start);
    have at(m4, r2.start) == at(z2, second->start);
    have r2.start == at(z2, second->start) by {
        normalize() using { r2.start == at(m4, r2.start); at(m4, r2.start) == at(z2, second->start); };
    }
    have r2.end == at(m4, r2.end);
    have at(m4, r2.end) == at(z2, second->end);
    have r2.end == at(z2, second->end) by {
        normalize() using { r2.end == at(m4, r2.end); at(m4, r2.end) == at(z2, second->end); };
    }
    have second_value == 22;
    have first_value == 11;
    step();
    have value == 33;
    have second->arena == arena;
    have second->arena->capacity == at(m4, second->arena->capacity);
    have arena->capacity == second->arena->capacity;
    have at(m4, second->arena->capacity) == at(m4, arena->capacity) by {
        solve() using {
            at(m4, second->arena) == arena;
        };
    }
    have arena->capacity == at(m4, arena->capacity) by {
        solve() using {
            arena->capacity == second->arena->capacity;
            second->arena->capacity == at(m4, second->arena->capacity);
            at(m4, second->arena->capacity) == at(m4, arena->capacity);
        };
    }
    have s0.capacity == at(m4, s0.capacity);
    have s0.capacity == arena->capacity;
    have forall (k: int32) {
        0 <= k and
            k < arena->capacity and
            (k < at(z1, first->start) or at(z1, first->end) <= k) and
            (k < at(z2, second->start) or at(z2, second->end) <= k) implies
            arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        extract(k < at(z1, first->start) or at(z1, first->end) <= k);
        extract(k < at(z2, second->start) or at(z2, second->end) <= k);
        have k < second->arena->capacity by {
            solve() using {
                k < arena->capacity;
                second->arena == arena;
            };
        }
        have second->arena->occupied[k] == at(m4, second->arena->occupied[k]) by {
            instantiate(forall (j: int32) {
                0 <= j and j < second->arena->capacity implies
                    second->arena->occupied[j] == at(m4, second->arena->occupied[j])
            }, k) using {
                0 <= k;
                k < second->arena->capacity;
            };
            assumption();
        }
        have at(m4, second->arena->occupied[k]) == at(m4, arena->occupied[k]) by {
            solve() using {
                at(m4, second->arena) == arena;
            };
        }
        have k < at(m4, arena->capacity) by {
            solve() using {
                k < arena->capacity;
                arena->capacity == at(m4, arena->capacity);
            };
        }
        have at(m4, arena->occupied[k]) == 0 by {
            instantiate(forall (j: int32) {
                0 <= j and
                    j < at(m4, arena->capacity) and
                    (j < at(z1, first->start) or at(z1, first->end) <= j) and
                    (j < at(z2, second->start) or at(z2, second->end) <= j) implies
                    at(m4, arena->occupied[j]) == 0
            }, k) using {
                0 <= k;
                k < at(m4, arena->capacity);
                k < at(z1, first->start) or at(z1, first->end) <= k;
                k < at(z2, second->start) or at(z2, second->end) <= k;
            };
            assumption();
        }
        solve() using {
            second->arena->occupied[k] == at(m4, second->arena->occupied[k]);
            at(m4, second->arena->occupied[k]) == at(m4, arena->occupied[k]);
            at(m4, arena->occupied[k]) == 0;
            second->arena == arena;
        };
    }
    have s0.live == 2;
    have 1 <= s0.live;
    have r2.end <= s0.capacity;
    have s0.capacity == arena->capacity;
    have r1.end <= s0.capacity by {
        have r1.end == at(m4, r1.end);
        have s0.capacity == at(m4, s0.capacity);
        have at(m4, r1.end) <= at(m4, s0.capacity);
        solve();
    }
    mark f2;
    let { after: g2 } = step(arena_free, { r: r2, st: s0 });
    have r1.start == at(f2, r1.start);
    have at(f2, r1.start) == at(z1, first->start);
    have r1.start == at(z1, first->start) by {
        normalize() using { r1.start == at(f2, r1.start); at(f2, r1.start) == at(z1, first->start); };
    }
    have r1.end == at(f2, r1.end);
    have at(f2, r1.end) == at(z1, first->end);
    have r1.end == at(z1, first->end) by {
        normalize() using { r1.end == at(f2, r1.end); at(f2, r1.end) == at(z1, first->end); };
    }
    have second->arena == arena;
    have second->arena->capacity == at(f2, second->arena->capacity);
    have arena->capacity == second->arena->capacity;
    have at(f2, second->arena->capacity) == at(f2, arena->capacity) by {
        solve() using {
            at(f2, second->arena) == arena;
        };
    }
    have arena->capacity == at(f2, arena->capacity) by {
        solve() using {
            arena->capacity == second->arena->capacity;
            second->arena->capacity == at(f2, second->arena->capacity);
            at(f2, second->arena->capacity) == at(f2, arena->capacity);
        };
    }
    have second->start == at(f2, r2.start);
    have at(f2, r2.start) == at(z2, second->start);
    have second->start == at(z2, second->start) by {
        normalize() using { second->start == at(f2, r2.start); at(f2, r2.start) == at(z2, second->start); };
    }
    have second->end == at(f2, r2.end);
    have at(f2, r2.end) == at(z2, second->end);
    have second->end == at(z2, second->end) by {
        normalize() using { second->end == at(f2, r2.end); at(f2, r2.end) == at(z2, second->end); };
    }
    have forall (k: int32) {
        0 <= k and
            k < arena->capacity and
            (k < at(z1, first->start) or at(z1, first->end) <= k) implies
            arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        extract(k < at(z1, first->start) or at(z1, first->end) <= k);
        have k < second->start implies arena->occupied[k] == 0 by {
            intro();
            have second->arena->occupied[k] == at(f2, second->arena->occupied[k]) by {
                instantiate(forall (j: int32) {
                    0 <= j and j < second->start implies
                        second->arena->occupied[j] == at(f2, second->arena->occupied[j])
                }, k) using {
                    0 <= k;
                    k < second->start;
                };
                assumption();
            }
            have at(f2, second->arena->occupied[k]) == at(f2, arena->occupied[k]) by {
                solve() using {
                    at(f2, second->arena) == arena;
                };
            }
            have k < at(f2, arena->capacity) by {
                solve() using {
                    k < arena->capacity;
                    arena->capacity == at(f2, arena->capacity);
                };
            }
            have k < at(z2, second->start);
            have k < at(z2, second->start) or at(z2, second->end) <= k;
            have at(f2, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) {
                    0 <= j and
                        j < at(f2, arena->capacity) and
                        (j < at(z1, first->start) or at(z1, first->end) <= j) and
                        (j < at(z2, second->start) or at(z2, second->end) <= j) implies
                        at(f2, arena->occupied[j]) == 0
                }, k) using {
                    0 <= k;
                    k < at(f2, arena->capacity);
                    k < at(z1, first->start) or at(z1, first->end) <= k;
                    k < at(z2, second->start) or at(z2, second->end) <= k;
                };
                assumption();
            }
            solve() using {
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
                instantiate(forall (j: int32) {
                    second->start <= j and j < second->end implies
                        second->arena->occupied[j] == 0
                }, k) using {
                    second->start <= k;
                    k < second->end;
                };
                solve() using {
                    second->arena->occupied[k] == 0;
                    second->arena == arena;
                };
            }
            assumption();
        }
        have second->end <= k implies arena->occupied[k] == 0 by {
            intro();
            have k < second->arena->capacity by {
                solve() using {
                    k < arena->capacity;
                    second->arena == arena;
                };
            }
            have second->arena->occupied[k] == at(f2, second->arena->occupied[k]) by {
                instantiate(forall (j: int32) {
                    second->end <= j and j < second->arena->capacity implies
                        second->arena->occupied[j] == at(f2, second->arena->occupied[j])
                }, k) using {
                    second->end <= k;
                    k < second->arena->capacity;
                };
                assumption();
            }
            have at(f2, second->arena->occupied[k]) == at(f2, arena->occupied[k]) by {
                solve() using {
                    at(f2, second->arena) == arena;
                };
            }
            have k < at(f2, arena->capacity) by {
                solve() using {
                    k < arena->capacity;
                    arena->capacity == at(f2, arena->capacity);
                };
            }
            have at(z2, second->end) <= k by {
                solve() using {
                    second->end <= k;
                    second->end == at(z2, second->end);
                };
            }
            have k < at(z2, second->start) or at(z2, second->end) <= k;
            have at(f2, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) {
                    0 <= j and
                        j < at(f2, arena->capacity) and
                        (j < at(z1, first->start) or at(z1, first->end) <= j) and
                        (j < at(z2, second->start) or at(z2, second->end) <= j) implies
                        at(f2, arena->occupied[j]) == 0
                }, k) using {
                    0 <= k;
                    k < at(f2, arena->capacity);
                    k < at(z1, first->start) or at(z1, first->end) <= k;
                    k < at(z2, second->start) or at(z2, second->end) <= k;
                };
                assumption();
            }
            solve() using {
                second->arena->occupied[k] == at(f2, second->arena->occupied[k]);
                at(f2, second->arena->occupied[k]) == at(f2, arena->occupied[k]);
                at(f2, arena->occupied[k]) == 0;
                second->arena == arena;
            };
        }
        if k < second->start {
            have k < second->start;
            extract(arena->occupied[k] == 0);
        } else {
            have second->start <= k;
            if k < second->end {
                have second->start <= k and k < second->end;
                extract(arena->occupied[k] == 0);
            } else {
                have second->end <= k;
                extract(arena->occupied[k] == 0);
            }
        }
    }
    have g2.live == 1;
    have 1 <= g2.live;
    have g2.capacity == at(f2, s0.capacity);
    have at(f2, s0.capacity) == at(f2, arena->capacity);
    have g2.capacity == arena->capacity;
    have r1.end <= g2.capacity by {
        have r1.end == at(f2, r1.end);
        have at(f2, r1.end) <= at(f2, s0.capacity);
        solve();
    }
    have first->arena == arena;
    mark f3;
    let { after: g3 } = step(arena_free, { r: r1, st: g2 });
    have first->arena == arena by {
        solve() using {
            first->arena == at(f3, first->arena);
            at(f3, first->arena) == arena;
        };
    }
    have first->arena->capacity == at(f3, first->arena->capacity);
    have arena->capacity == first->arena->capacity;
    have at(f3, first->arena->capacity) == at(f3, arena->capacity);
    have arena->capacity == at(f3, arena->capacity) by {
        solve() using {
            arena->capacity == first->arena->capacity;
            first->arena->capacity == at(f3, first->arena->capacity);
            at(f3, first->arena->capacity) == at(f3, arena->capacity);
        };
    }
    have first->start == at(f3, r1.start);
    have at(f3, r1.start) == at(z1, first->start);
    have first->start == at(z1, first->start) by {
        normalize() using { first->start == at(f3, r1.start); at(f3, r1.start) == at(z1, first->start); };
    }
    have first->end == at(f3, r1.end);
    have at(f3, r1.end) == at(z1, first->end);
    have first->end == at(z1, first->end) by {
        normalize() using { first->end == at(f3, r1.end); at(f3, r1.end) == at(z1, first->end); };
    }
    have forall (k: int32) {
        0 <= k and
            k < arena->capacity implies
            arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        have k < first->start implies arena->occupied[k] == 0 by {
            intro();
            have first->arena->occupied[k] == at(f3, first->arena->occupied[k]) by {
                instantiate(forall (j: int32) {
                    0 <= j and j < first->start implies
                        first->arena->occupied[j] == at(f3, first->arena->occupied[j])
                }, k) using {
                    0 <= k;
                    k < first->start;
                };
                assumption();
            }
            have at(f3, first->arena->occupied[k]) == at(f3, arena->occupied[k]) by {
                solve() using {
                    at(f3, first->arena) == arena;
                };
            }
            have k < at(f3, arena->capacity);
            have k < at(z1, first->start);
            have k < at(z1, first->start) or at(z1, first->end) <= k;
            have at(f3, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) {
                    0 <= j and
                        j < at(f3, arena->capacity) and
                        (j < at(z1, first->start) or at(z1, first->end) <= j) implies
                        at(f3, arena->occupied[j]) == 0
                }, k) using {
                    0 <= k;
                    k < at(f3, arena->capacity);
                    k < at(z1, first->start) or at(z1, first->end) <= k;
                };
                assumption();
            }
            solve() using {
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
                instantiate(forall (j: int32) {
                    first->start <= j and j < first->end implies
                        first->arena->occupied[j] == 0
                }, k) using {
                    first->start <= k;
                    k < first->end;
                };
                solve() using {
                    first->arena->occupied[k] == 0;
                    first->arena == arena;
                };
            }
            assumption();
        }
        have first->end <= k implies arena->occupied[k] == 0 by {
            intro();
            have k < first->arena->capacity;
            have first->arena->occupied[k] == at(f3, first->arena->occupied[k]) by {
                instantiate(forall (j: int32) {
                    first->end <= j and j < first->arena->capacity implies
                        first->arena->occupied[j] == at(f3, first->arena->occupied[j])
                }, k) using {
                    first->end <= k;
                    k < first->arena->capacity;
                };
                assumption();
            }
            have at(f3, first->arena->occupied[k]) == at(f3, arena->occupied[k]) by {
                solve() using {
                    at(f3, first->arena) == arena;
                };
            }
            have k < at(f3, arena->capacity);
            have at(z1, first->end) <= k;
            have k < at(z1, first->start) or at(z1, first->end) <= k;
            have at(f3, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) {
                    0 <= j and
                        j < at(f3, arena->capacity) and
                        (j < at(z1, first->start) or at(z1, first->end) <= j) implies
                        at(f3, arena->occupied[j]) == 0
                }, k) using {
                    0 <= k;
                    k < at(f3, arena->capacity);
                    k < at(z1, first->start) or at(z1, first->end) <= k;
                };
                assumption();
            }
            solve() using {
                first->arena->occupied[k] == at(f3, first->arena->occupied[k]);
                at(f3, first->arena->occupied[k]) == at(f3, arena->occupied[k]);
                at(f3, arena->occupied[k]) == 0;
                first->arena == arena;
            };
        }
        if k < first->start {
            have k < first->start;
            extract(arena->occupied[k] == 0);
        } else {
            have first->start <= k;
            if k < first->end {
                have first->start <= k and k < first->end;
                extract(arena->occupied[k] == 0);
            } else {
                have first->end <= k;
                extract(arena->occupied[k] == 0);
            }
        }
    }
    have g3.live == 0;
    have g3.live < 2147483647 by {
        solve() using {
            g3.live == 0;
        };
    }
    mark a3;
    let { outcome: o3 } = step(arena_alloc, { st: g3 });
    have arena->capacity == at(a3, arena->capacity);
    branch {
        have o3.model == ArenaAllocOutcome::Failure;
        have forall (k: int32) {
            0 <= k and k < arena->capacity implies arena->occupied[k] == 0
        } by {
            intro();
            intro();
            extract(0 <= k);
            extract(k < arena->capacity);
            have arena->occupied[k] == at(a3, arena->occupied[k]) by {
                instantiate(forall (j: int32) {
                    allocated == 0 and 0 <= j and j < arena->capacity implies
                        arena->occupied[j] == at(a3, arena->occupied[j])
                }, k) using {
                    allocated == 0;
                    0 <= k;
                    k < arena->capacity;
                };
                assumption();
            }
            have k < at(a3, arena->capacity);
            have at(a3, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) {
                    0 <= j and j < at(a3, arena->capacity) implies
                        at(a3, arena->occupied[j]) == 0
                }, k) using {
                    0 <= k;
                    k < at(a3, arena->capacity);
                };
                assumption();
            }
            solve() using {
                arena->occupied[k] == at(a3, arena->occupied[k]);
                at(a3, arena->occupied[k]) == 0;
            };
        }
        step(arena_destroy, { st: g3 });
        unfold(o3);
        step_until(function.exit);
        solve();
    } else {}
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
    have o3.model == ArenaAllocOutcome::Success(combined->start, combined->end);
    have 0 <= combined->start;
    have combined->start < combined->end;
    have combined->end <= arena->capacity;
    have arena->capacity <= 536870911;
    have combined->start < 536870911;

    have g3.live == 1;
    let { allocated: r3 } = unfold(o3);
    mark z3;
    have r3.start == at(z3, combined->start);
    have r3.end == at(z3, combined->end);
    have forall (k: int32) {
        0 <= k and k < arena->capacity and (k < at(z3, combined->start) or at(z3, combined->end) <= k) implies
            arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        extract(k < at(z3, combined->start) or at(z3, combined->end) <= k);
        have k < at(a3, arena->capacity);
        have at(a3, arena->occupied[k]) == 0 by {
            instantiate(forall (j: int32) {
                0 <= j and j < at(a3, arena->capacity) implies
                    at(a3, arena->occupied[j]) == 0
            }, k) using {
                0 <= k;
                k < at(a3, arena->capacity);
            };
            assumption();
        }
        cases {
            k < at(z3, combined->start) => {
                have k < combined->start;
                have arena->occupied[k] == at(a3, arena->occupied[k]) by {
                    instantiate(forall (j: int32) {
                        allocated == 1 and 0 <= j and j < combined->start implies
                            arena->occupied[j] == at(a3, arena->occupied[j])
                    }, k) using {
                        allocated == 1;
                        0 <= k;
                        k < combined->start;
                    };
                    assumption();
                }
                solve() using {
                    arena->occupied[k] == at(a3, arena->occupied[k]);
                    at(a3, arena->occupied[k]) == 0;
                };
            }
            at(z3, combined->end) <= k => {
                have combined->end <= k;
                have arena->occupied[k] == at(a3, arena->occupied[k]) by {
                    instantiate(forall (j: int32) {
                        allocated == 1 and combined->end <= j and j < arena->capacity implies
                            arena->occupied[j] == at(a3, arena->occupied[j])
                    }, k) using {
                        allocated == 1;
                        combined->end <= k;
                        k < arena->capacity;
                    };
                    assumption();
                }
                solve() using {
                    arena->occupied[k] == at(a3, arena->occupied[k]);
                    at(a3, arena->occupied[k]) == 0;
                };
            }
        }
    }
    have combined->arena == arena;
    have g3.capacity == arena->capacity;
    have 0 <= r3.start;
    have r3.start < 536870911;
    have r3.start < 2147483643;
    have r3.start <= 2147483643;
    have defined(r3.start + 4);
    have at(z3, combined->start) == r3.start by {
        solve() using {
            r3.start == at(z3, combined->start);
        };
    }
    have defined(at(z3, combined->start) + 4);
    have to_integer(at(z3, combined->start) + 4) == to_integer(at(z3, combined->start)) + 4;
    have to_integer(at(z3, combined->end)) == to_integer(at(z3, combined->start) + 4) by solve();
    have at(z3, combined->end) == at(z3, combined->start) + 4 by solve() using {
        to_integer(at(z3, combined->end)) == to_integer(at(z3, combined->start) + 4);
        to_integer(at(z3, combined->start) + 4) == to_integer(at(z3, combined->start)) + 4;
    };
    have r3.end == r3.start + 4 by {
        solve() using {
            r3.start == at(z3, combined->start);
            r3.end == at(z3, combined->end);
            at(z3, combined->end) == at(z3, combined->start) + 4;
        };
    }
    have r3.end <= g3.capacity;
    have r3.start <= 2147483644;
    have defined(r3.start + 3);
    have r3.start + 3 < r3.end;
    have value == 33;
    mark w3;
    step(arena_write, { r: r3, st: g3 });
    have r3.start == at(w3, r3.start);
    have defined(r3.start + 3);
    have combined->arena->data[r3.start + 3] == value;
    have combined->arena == arena;
    have combined->arena->capacity == at(w3, combined->arena->capacity);
    have arena->capacity == combined->arena->capacity;
    have at(w3, combined->arena->capacity) == at(w3, arena->capacity);
    have arena->capacity == at(w3, arena->capacity);
    have g3.capacity == at(w3, g3.capacity);
    have g3.capacity == arena->capacity;
    have forall (k: int32) {
        0 <= k and
            k < arena->capacity and
            (k < at(z3, combined->start) or at(z3, combined->end) <= k) implies
            arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        extract(k < at(z3, combined->start) or at(z3, combined->end) <= k);
        have k < combined->arena->capacity;
        have combined->arena->occupied[k] == at(w3, combined->arena->occupied[k]) by {
            instantiate(forall (j: int32) {
                0 <= j and j < combined->arena->capacity implies
                    combined->arena->occupied[j] == at(w3, combined->arena->occupied[j])
            }, k) using {
                0 <= k;
                k < combined->arena->capacity;
            };
            assumption();
        }
        have at(w3, combined->arena->occupied[k]) == at(w3, arena->occupied[k]);
        have k < at(w3, arena->capacity);
        have at(w3, arena->occupied[k]) == 0 by {
            instantiate(forall (j: int32) {
                0 <= j and
                    j < at(w3, arena->capacity) and
                    (j < at(z3, combined->start) or at(z3, combined->end) <= j) implies
                    at(w3, arena->occupied[j]) == 0
            }, k) using {
                0 <= k;
                k < at(w3, arena->capacity);
                k < at(z3, combined->start) or at(z3, combined->end) <= k;
            };
            assumption();
        }
        solve() using {
            combined->arena->occupied[k] == at(w3, combined->arena->occupied[k]);
            at(w3, combined->arena->occupied[k]) == at(w3, arena->occupied[k]);
            at(w3, arena->occupied[k]) == 0;
            combined->arena == arena;
        };
    }
    have g3.live == at(w3, g3.live);
    have g3.live == 1;
    have r3.start == at(w3, r3.start);
    have r3.end == at(w3, r3.end);
    have r3.start == at(z3, combined->start);
    have r3.end == at(z3, combined->end);
    have r3.end <= g3.capacity by {
        have r3.end <= at(w3, g3.capacity);
        solve() using {
            r3.end <= at(w3, g3.capacity);
            g3.capacity == at(w3, g3.capacity);
        };
    }
    have defined(r3.start + 3);
    have r3.start + 3 < r3.end;
    have combined->arena->data[r3.start + 3] == 33;
    mark m5;
    step(arena_read, { r: r3, st: g3 });
    have value == at(m5, combined->arena->data[r3.start + 3]);
    have value == 33;
    have combined->arena == arena;
    have combined->arena->capacity == at(m5, combined->arena->capacity);
    have arena->capacity == combined->arena->capacity;
    have at(m5, combined->arena->capacity) == at(m5, arena->capacity);
    have arena->capacity == at(m5, arena->capacity);
    have g3.capacity == at(m5, g3.capacity);
    have g3.capacity == arena->capacity;
    have forall (k: int32) {
        0 <= k and
            k < arena->capacity and
            (k < at(z3, combined->start) or at(z3, combined->end) <= k) implies
            arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        extract(k < at(z3, combined->start) or at(z3, combined->end) <= k);
        have k < combined->arena->capacity;
        have combined->arena->occupied[k] == at(m5, combined->arena->occupied[k]) by {
            instantiate(forall (j: int32) {
                0 <= j and j < combined->arena->capacity implies
                    combined->arena->occupied[j] == at(m5, combined->arena->occupied[j])
            }, k) using {
                0 <= k;
                k < combined->arena->capacity;
            };
            assumption();
        }
        have at(m5, combined->arena->occupied[k]) == at(m5, arena->occupied[k]);
        have k < at(m5, arena->capacity);
        have at(m5, arena->occupied[k]) == 0 by {
            instantiate(forall (j: int32) {
                0 <= j and
                    j < at(m5, arena->capacity) and
                    (j < at(z3, combined->start) or at(z3, combined->end) <= j) implies
                    at(m5, arena->occupied[j]) == 0
            }, k) using {
                0 <= k;
                k < at(m5, arena->capacity);
                k < at(z3, combined->start) or at(z3, combined->end) <= k;
            };
            assumption();
        }
        solve() using {
            combined->arena->occupied[k] == at(m5, combined->arena->occupied[k]);
            at(m5, combined->arena->occupied[k]) == at(m5, arena->occupied[k]);
            at(m5, arena->occupied[k]) == 0;
            combined->arena == arena;
        };
    }
    have g3.live == 1;
    have 1 <= g3.live;
    have r3.start == at(z3, combined->start);
    have r3.end == at(z3, combined->end);
    have r3.end <= g3.capacity by {
        have r3.end == at(m5, r3.end);
        have r3.end <= at(m5, g3.capacity);
        solve() using {
            r3.end <= at(m5, g3.capacity);
            g3.capacity == at(m5, g3.capacity);
        };
    }
    mark f4;
    let { after: g4 } = step(arena_free, { r: r3, st: g3 });
    have combined->arena == arena;
    have combined->arena->capacity == at(f4, combined->arena->capacity);
    have arena->capacity == combined->arena->capacity;
    have at(f4, combined->arena->capacity) == at(f4, arena->capacity);
    have arena->capacity == at(f4, arena->capacity);
    have combined->start == at(z3, combined->start);
    have combined->end == at(z3, combined->end);
    have forall (k: int32) {
        0 <= k and
            k < arena->capacity implies
            arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        have k < combined->start implies arena->occupied[k] == 0 by {
            intro();
            have combined->arena->occupied[k] == at(f4, combined->arena->occupied[k]) by {
                instantiate(forall (j: int32) {
                    0 <= j and j < combined->start implies
                        combined->arena->occupied[j] == at(f4, combined->arena->occupied[j])
                }, k) using {
                    0 <= k;
                    k < combined->start;
                };
                assumption();
            }
            have at(f4, combined->arena->occupied[k]) == at(f4, arena->occupied[k]) by {
                solve() using {
                    at(f4, combined->arena) == arena;
                };
            }
            have k < at(f4, arena->capacity) by {
                solve() using {
                    k < arena->capacity;
                    arena->capacity == at(f4, arena->capacity);
                };
            }
            have k < at(z3, combined->start) by {
                solve() using {
                    k < combined->start;
                    combined->start == at(z3, combined->start);
                };
            }
            have k < at(z3, combined->start) or at(z3, combined->end) <= k;
            have at(f4, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) {
                    0 <= j and
                        j < at(f4, arena->capacity) and
                        (j < at(z3, combined->start) or at(z3, combined->end) <= j) implies
                        at(f4, arena->occupied[j]) == 0
                }, k) using {
                    0 <= k;
                    k < at(f4, arena->capacity);
                    k < at(z3, combined->start) or at(z3, combined->end) <= k;
                };
                assumption();
            }
            solve() using {
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
                instantiate(forall (j: int32) {
                    combined->start <= j and j < combined->end implies
                        combined->arena->occupied[j] == 0
                }, k) using {
                    combined->start <= k;
                    k < combined->end;
                };
                solve() using {
                    combined->arena->occupied[k] == 0;
                    combined->arena == arena;
                };
            }
            assumption();
        }
        have combined->end <= k implies arena->occupied[k] == 0 by {
            intro();
            have k < combined->arena->capacity by {
                solve() using {
                    k < arena->capacity;
                    combined->arena == arena;
                };
            }
            have combined->arena->occupied[k] == at(f4, combined->arena->occupied[k]) by {
                instantiate(forall (j: int32) {
                    combined->end <= j and j < combined->arena->capacity implies
                        combined->arena->occupied[j] == at(f4, combined->arena->occupied[j])
                }, k) using {
                    combined->end <= k;
                    k < combined->arena->capacity;
                };
                assumption();
            }
            have at(f4, combined->arena->occupied[k]) == at(f4, arena->occupied[k]) by {
                solve() using {
                    at(f4, combined->arena) == arena;
                };
            }
            have k < at(f4, arena->capacity) by {
                solve() using {
                    k < arena->capacity;
                    arena->capacity == at(f4, arena->capacity);
                };
            }
            have at(z3, combined->end) <= k by {
                solve() using {
                    combined->end <= k;
                    combined->end == at(z3, combined->end);
                };
            }
            have k < at(z3, combined->start) or at(z3, combined->end) <= k;
            have at(f4, arena->occupied[k]) == 0 by {
                instantiate(forall (j: int32) {
                    0 <= j and
                        j < at(f4, arena->capacity) and
                        (j < at(z3, combined->start) or at(z3, combined->end) <= j) implies
                        at(f4, arena->occupied[j]) == 0
                }, k) using {
                    0 <= k;
                    k < at(f4, arena->capacity);
                    k < at(z3, combined->start) or at(z3, combined->end) <= k;
                };
                assumption();
            }
            solve() using {
                combined->arena->occupied[k] == at(f4, combined->arena->occupied[k]);
                at(f4, combined->arena->occupied[k]) == at(f4, arena->occupied[k]);
                at(f4, arena->occupied[k]) == 0;
                combined->arena == arena;
            };
        }
        if k < combined->start {
            have k < combined->start;
            extract(arena->occupied[k] == 0);
        } else {
            have combined->start <= k;
            if k < combined->end {
                have combined->start <= k and k < combined->end;
                extract(arena->occupied[k] == 0);
            } else {
                have combined->end <= k;
                extract(arena->occupied[k] == 0);
            }
        }
    }
    step(arena_destroy, { st: g4 });
    step_until(function.exit);
    solve();
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
