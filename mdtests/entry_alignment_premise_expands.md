# An entry alignment fact cited after a loop expands in its source spelling

This is `arena_init` from `examples/arena`, its C unchanged, with only the
resources its own contract names. `consumes *arena` gives the
function-entry fact `aligned(arena, 8)`. Expanding the `close()` that closes
the loop's `maintain` proof once cited that fact as a premise read at
function entry.

The fact is `address(arena) & 7u64 == 0u64` inside, and the expansion wrote
it with each side read at entry, as
`at(function.entry, ((arena as uint64) & 7u64)) == at(function.entry, 0u64)`.
Click has no cast spelling for a pointer's address, so the rewrite did not
parse and `click audit examples/arena` failed at that site while
`click verify` accepted the proof. A state-read alignment fact now renders
as `at(function.entry, aligned(arena, 8))`, which
`state_read_alignment_fact_renders_as_aligned` in
`src/surface/tests/surface_syntax.rs` checks directly. The expansion no longer
needs the fact at all: the loop's store `occupied[i - 1]` and an earlier cell
`occupied[k]` are separated by `k < i - 1` alone. The maintenance proof
instantiates the previous prefix invariant and preserves each earlier cell
across the recorded store. It checks the newly written cell directly. The
loop also follows a proof-level `branch`, the shape
`loop_after_proof_branch_expands.md` reduces.
The expansion regression in `src/surface/tests/expansion_tests.rs` expands
the site and re-verifies the rewrite. The retained-session audit regression
uses the smaller `loop_after_proof_branch_expands.md` fixture rather than
repeatedly checking this entire allocation proof.

```c filename=arena_init.c
struct arena {
    int32* data;
    int32* occupied;
    int32 capacity;
    int32 live_regions;
};

int32 arena_init(struct arena* arena, int32 capacity) {
    int32* data;
    int32* occupied;
    int32 i;

    arena->data = 0;
    arena->occupied = 0;
    arena->capacity = 0;
    arena->live_regions = 0;

    if (capacity <= 0) {
        return 0;
    }
    if (capacity > 536870911) {
        return 0;
    }

    data = malloc(capacity * 4);
    if (data == 0) {
        return 0;
    }

    occupied = malloc(capacity * 4);
    if (occupied == 0) {
        free(data);
        return 0;
    }

    i = 0;
    while (i < capacity) {
        occupied[i] = 0;
        i = i + 1;
    }

    arena->data = data;
    arena->occupied = occupied;
    arena->capacity = capacity;
    return 1;
}
```

```click
import click::separation;

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

resource arena_initialized_access(
    data: int32*,
    occupied: int32*,
    capacity: int32,
    initialized: int32
) {
    if initialized == 1 {
        owns data[0..capacity];
        owns occupied[0..capacity];
    }
}

resource arena_init_result(arena: struct arena*, initialized: int32) {
    owns *arena;
    owns arena_initialized_storage(
        arena->data,
        arena->occupied,
        arena->capacity,
        initialized
    );
    fact initialized == 0 or initialized == 1;
    fact initialized == 0 implies arena->data == 0;
    fact initialized == 0 implies arena->occupied == 0;
    fact initialized == 0 implies arena->capacity == 0;
    fact initialized == 0 implies arena->live_regions == 0;
    fact initialized == 1 implies arena->live_regions == 0;
}


verifying "arena_init.c";

int32 arena_init(struct arena* arena, int32 capacity) {
    consumes *arena;
    produces arena_init_result(arena, result);
    produces arena_initialized_access(
        arena->data,
        arena->occupied,
        arena->capacity,
        result
    );

    ensures result == 0 or result == 1;
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
        true => {
            step();
            fold(arena_initialized_storage(
                arena->data,
                arena->occupied,
                arena->capacity,
                result
            ));
            fold(arena_initialized_access(
                arena->data,
                arena->occupied,
                arena->capacity,
                result
            ));
            fold(arena_init_result(arena, result));
            close();
        }
        false => {}
    }
    branch {
        true => {
            step();
            fold(arena_initialized_storage(
                arena->data,
                arena->occupied,
                arena->capacity,
                result
            ));
            fold(arena_initialized_access(
                arena->data,
                arena->occupied,
                arena->capacity,
                result
            ));
            fold(arena_init_result(arena, result));
            close();
        }
        false => {}
    }
    step();
    branch {
        true => {
            step();
            fold(arena_initialized_storage(
                arena->data,
                arena->occupied,
                arena->capacity,
                result
            ));
            fold(arena_initialized_access(
                arena->data,
                arena->occupied,
                arena->capacity,
                result
            ));
            fold(arena_init_result(arena, result));
            close();
        }
        false => {}
    }
    step();
    branch {
        true => {
            step();
            step();
            fold(arena_initialized_storage(
                arena->data,
                arena->occupied,
                arena->capacity,
                result
            ));
            fold(arena_initialized_access(
                arena->data,
                arena->occupied,
                arena->capacity,
                result
            ));
            fold(arena_init_result(arena, result));
            close();
        }
        false => {}
    }
    have 1 <= capacity by {
        close() using {
            not (capacity <= 0);
        };
    }
    have capacity <= 536870911 by {
        close() using {
            not (capacity > 536870911);
        };
    }
    step();
    loop initialize_occupied {
        decreases to_integer(capacity) - to_integer(i);
        invariant 0 <= i and i <= capacity;
        invariant forall (k: int32) {
            0 <= k and k < i implies occupied[k] == 0
        };
        owns occupied[0..capacity];

        initialize by close();
        maintain by {
            mark iteration;
            step();
            step();
            have to_integer(at(iteration, i) + 1) == to_integer(at(iteration, i)) + 1;
            have 0 <= to_integer(capacity) - to_integer(at(iteration, i) + 1);
            have forall (k: int32) { 0 <= k and k < i implies occupied[k] == 0 } by {
                intro() {
                    intro() {
                        have 0 <= k;
                        have k < i;
                        if k < at(iteration, i) {
                            have at(iteration, occupied[k]) == 0 by {
                                have at(iteration, 0) <= at(iteration, k) and at(iteration, k) < at(iteration, i);
                                instantiate(forall (j: int32) {
                                    at(iteration, 0) <= at(iteration, j) and at(iteration, j) < at(iteration, i) implies
                                        at(iteration, occupied[j]) == at(iteration, 0)
                                }, k);
                                close();
                            }
                            have at(iteration, i) != k by { close() using { k < at(iteration, i); }; }
                            have at(iteration, separate(memory(occupied[i]), memory(occupied[k]))) by {
                                apply(separation::separate_elements(occupied, at(iteration, i), k));
                            }
                            have separate(loop(0).statement(0).footprint, memory(occupied[k])) by {
                                close() using { at(iteration, separate(memory(occupied[i]), memory(occupied[k]))); };
                            }
                            have at(loop(0).statement(0).exit, occupied[k]) == at(iteration, occupied[k]) by {
                                preserve(memory(occupied[k]), loop(0).statement(0));
                            }
                            have separate(loop(0).statement(1).footprint, memory(occupied[k])) by { close() using {}; }
                            have occupied[k] == at(loop(0).statement(1).entry, occupied[k]) by {
                                preserve(memory(occupied[k]), loop(0).statement(1));
                            }
                            close();
                        } else {
                            have k == at(iteration, i) by { close(); }
                            rewrite(k, at(iteration, i));
                            close();
                        }
                    }
                }
            }
            close();
        }
    }
    have i == capacity;
    have forall (k: int32) {
        0 <= k and k < capacity implies occupied[k] == 0
    } by {
        intro() {
            intro() {
                have 0 <= k and k < i;
                instantiate(forall (j: int32) {
                    0 <= j and j < i implies occupied[j] == 0
                }, k);
                close();
            }
        }
    }
    step();
    step();
    step();
    have forall (k: int32) {
        0 <= k and k < arena->capacity implies arena->occupied[k] == 0
    } by {
        intro() {
            intro() {
                have k < capacity by {
                    close();
                }
                instantiate(forall (j: int32) {
                    0 <= j and j < capacity implies occupied[j] == 0
                }, k);
                close();
            }
        }
    }
    step();
    have result == 1 by {
        close();
    }
    have result == 0 or result == 1 by {
        close();
    }
    have forall (k: int32) {
        result == 1 and 0 <= k and k < arena->capacity implies
            arena->occupied[k] == 0
    } by {
        intro() {
            intro() {
                instantiate(forall (j: int32) {
                    0 <= j and j < arena->capacity implies arena->occupied[j] == 0
                }, k);
                close();
            }
        }
    }
    fold(arena_initialized_storage(
        arena->data,
        arena->occupied,
        arena->capacity,
        result
    ));
    fold(arena_initialized_access(
        arena->data,
        arena->occupied,
        arena->capacity,
        result
    ));
    fold(arena_init_result(arena, result));
    close();
    close();
    close();
    close();
}

```

```expect
pass
```
