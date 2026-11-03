# Return descriptor-backed elements to iterated ownership across a loop

The occupied-cell store makes the guard true. `give` returns the corresponding
owned suffix element through a fresh descriptor read. Keep the descriptor
access and loop: a single-store control does not reproduce the recovery bug.
The explicit field and separation facts support the later window fold.

```c filename=probe.c
struct arena { int32* data; int32* occupied; int32 capacity; };
void release_run(struct arena* arena, int32 start, int32 end) {
    int32 i;
    i = start;
    while (i < end) {
        arena->occupied[i] = 0;
        i = i + 1;
    }
}
```

```click
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

resource arena_cells(data: int32*, occupied: int32*, capacity: int32) {
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
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


verifying "probe.c";
void release_run(struct arena* arena, int32 start, int32 end) {
    views arena->data; views arena->occupied; views arena->capacity;
    consumes w: arena_clear_window(arena->data, arena->occupied, arena->capacity, start, end);
    requires w.next == start;
    requires arena->capacity <= 536870911;
    produces arena_cells(arena->data, arena->occupied, arena->capacity);
} by {
    let { next: initial_next } = unfold(w);
    have 0 <= arena->capacity by { solve(); }
    have separate(memory(arena->occupied[0..arena->capacity]), memory(arena->data)) by { solve(); }
    have separate(memory(arena->occupied[0..arena->capacity]), memory(arena->occupied)) by { solve(); }
    have separate(memory(arena->occupied[0..arena->capacity]), memory(arena->capacity)) by { solve(); }
    let w = fold(arena_clear_window(arena->data, arena->occupied, arena->capacity, start, end), { next: initial_next });
    step(); step();
    loop as clear_occupied {
        decreases end - i;
        owns w: arena_clear_window(arena->data, arena->occupied, arena->capacity, start, end);
        invariant w.next == i;
        invariant separate(memory(arena->occupied[0..arena->capacity]), memory(arena->data));
        invariant separate(memory(arena->occupied[0..arena->capacity]), memory(arena->occupied));
        invariant separate(memory(arena->occupied[0..arena->capacity]), memory(arena->capacity));

        invariant forall (k: int32) {
            0 <= k and k < start implies
                arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k])
        };
        invariant forall (k: int32) {
            end <= k and k < arena->capacity implies
                arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k])
        };
        initialize by solve();
        preserve by {
            let { next: m } = unfold(w);
            have m == i;
            have 0 <= start;
            have start <= m;
            have start <= i;
            have 0 <= i;
            have end <= arena->capacity;
            have i < arena->capacity;
            have 0 < arena->capacity by { solve(); }
            have separate(memory(arena->occupied[0..arena->capacity]), memory(arena->data)) by { assumption(); }
            have separate(memory(arena->occupied[i]), memory(arena->data)) by {
                apply(separation::separate_symm(memory(arena->occupied[0..arena->capacity]), memory(arena->data))) using {
                    separate(memory(arena->occupied[0..arena->capacity]), memory(arena->data));
                };
                apply(separation::contains_refl(memory(arena->data))) using {};
                apply(selected_array_cell(memory(arena->data), memory(arena->data), arena->occupied, arena->capacity, i)) using {
                    separate(memory(arena->data), memory(arena->occupied[0..arena->capacity]));
                    contains(memory(arena->data), memory(arena->data)); 0 <= i; i < arena->capacity;
                };
                apply(separation::separate_symm(memory(arena->data), memory(arena->occupied[i]))) using {
                    separate(memory(arena->data), memory(arena->occupied[i]));
                };
            }
            have separate(memory(arena->occupied[i]), memory(arena->occupied)) by {
                apply(separation::separate_symm(memory(arena->occupied[0..arena->capacity]), memory(arena->occupied))) using {
                    separate(memory(arena->occupied[0..arena->capacity]), memory(arena->occupied));
                };
                apply(separation::contains_refl(memory(arena->occupied))) using {};
                apply(selected_array_cell(memory(arena->occupied), memory(arena->occupied), arena->occupied, arena->capacity, i)) using {
                    separate(memory(arena->occupied), memory(arena->occupied[0..arena->capacity]));
                    contains(memory(arena->occupied), memory(arena->occupied)); 0 <= i; i < arena->capacity;
                };
                apply(separation::separate_symm(memory(arena->occupied), memory(arena->occupied[i]))) using {
                    separate(memory(arena->occupied), memory(arena->occupied[i]));
                };
            }
            have separate(memory(arena->occupied[i]), memory(arena->capacity)) by {
                apply(separation::separate_symm(memory(arena->occupied[0..arena->capacity]), memory(arena->capacity))) using {
                    separate(memory(arena->occupied[0..arena->capacity]), memory(arena->capacity));
                };
                apply(separation::contains_refl(memory(arena->capacity))) using {};
                apply(selected_array_cell(memory(arena->capacity), memory(arena->capacity), arena->occupied, arena->capacity, i)) using {
                    separate(memory(arena->capacity), memory(arena->occupied[0..arena->capacity]));
                    contains(memory(arena->capacity), memory(arena->capacity)); 0 <= i; i < arena->capacity;
                };
                apply(separation::separate_symm(memory(arena->capacity), memory(arena->occupied[i]))) using {
                    separate(memory(arena->capacity), memory(arena->occupied[i]));
                };
            }
            mark opened;
            step();
            have at(opened, separate(loop(0).statement(0).footprint, memory(arena->data))) by {
                normalize() using { at(opened, separate(memory(arena->occupied[i]), memory(arena->data))); };
            }
            have arena->data == at(opened, arena->data) by {
                transport_certificate {
                    premise 0: at(opened, separate(loop(0).statement(0).footprint, memory(arena->data))) => at(opened, separate(loop(0).statement(0).footprint, memory(arena->data)));
                    preserve 0 => arena->data == at(opened, arena->data);
                    conclusion 1;
                }
            }
            have at(opened, separate(loop(0).statement(0).footprint, memory(arena->occupied))) by {
                normalize() using { at(opened, separate(memory(arena->occupied[i]), memory(arena->occupied))); };
            }
            have arena->occupied == at(opened, arena->occupied) by {
                transport_certificate {
                    premise 0: at(opened, separate(loop(0).statement(0).footprint, memory(arena->occupied))) => at(opened, separate(loop(0).statement(0).footprint, memory(arena->occupied)));
                    preserve 0 => arena->occupied == at(opened, arena->occupied);
                    conclusion 1;
                }
            }
            have at(opened, separate(loop(0).statement(0).footprint, memory(arena->capacity))) by {
                normalize() using { at(opened, separate(memory(arena->occupied[i]), memory(arena->capacity))); };
            }
            have arena->capacity == at(opened, arena->capacity) by { assumption(); }
            give(arena->data[i..i + 1]);
            step();
            have to_integer(start) <= to_integer(at(opened, i) + 1);
            have forall (k: int32) {
                start <= k and to_integer(k) < to_integer(at(opened, i) + 1) implies arena->occupied[k] == 0
            } by {
                intro();
                intro();
                extract(start <= k);
                extract(to_integer(k) < to_integer(at(opened, i) + 1));
                if k < at(opened, i) {
                    have k < m;
                    have at(opened, arena->occupied[k]) == 0 by {
                        instantiate(forall (j: int32) {
                            at(opened, start) <= at(opened, j) and
                                at(opened, j) < at(opened, m) implies
                                at(opened, arena->occupied[j]) == at(opened, 0)
                        }, k) using {
                            start <= k;
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
                    have k <= at(opened, i);
                    have k == at(opened, i);
                    rewrite(k == at(opened, i));
                    normalize();
                }
            }
            have forall (k: int32) {
                0 <= k and k < start implies
                    arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k])
            } by {
                intro();
                intro();
                extract(0 <= k);
                extract(k < start);
                have at(opened, arena->occupied[k]) ==
                    at(clear_occupied.entry, arena->occupied[k]) by {
                    instantiate(forall (j: int32) {
                        at(opened, 0) <= at(opened, j) and
                            at(opened, j) < at(opened, start) implies
                            at(opened, arena->occupied[j]) ==
                                at(clear_occupied.entry, arena->occupied[j])
                    }, k) using {
                        0 <= k;
                        k < start;
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
                end <= k and k < arena->capacity implies
                    arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k])
            } by {
                intro();
                intro();
                extract(end <= k);
                extract(k < arena->capacity);
                have at(opened, arena->occupied[k]) ==
                    at(clear_occupied.entry, arena->occupied[k]) by {
                    instantiate(forall (j: int32) {
                        at(opened, end) <= at(opened, j) and
                            at(opened, j) < at(opened, arena->capacity) implies
                            at(opened, arena->occupied[j]) ==
                                at(clear_occupied.entry, arena->occupied[j])
                    }, k) using {
                        end <= k;
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
            have arena->data == old(arena->data);
            have arena->occupied == old(arena->occupied);
            have arena->capacity == old(arena->capacity);
            have separate(memory(arena->occupied[0..arena->capacity]), memory(arena->data[0..arena->capacity])) by {
                rewrite(arena->data == old(arena->data));
                rewrite(arena->occupied == old(arena->occupied));
                rewrite(arena->capacity == old(arena->capacity));
                assumption();
            }
            let w = fold(arena_clear_window(arena->data, arena->occupied, arena->capacity, start, end), {
                next: at(opened, i) + 1
            });
            have start <= end;
        }
    }
    let { next: n } = unfold(w);
    have n <= end;
    have n == i;
    have not (n < end) by { rewrite(n == i); assumption(); }
    have n == end;
    step_until(function.exit);
    have arena->data == old(arena->data);
    have arena->occupied == old(arena->occupied);
    have arena->capacity == old(arena->capacity);
    fold(arena_cells(arena->data, arena->occupied, arena->capacity));
    solve();
}
```

```expect
pass
```
