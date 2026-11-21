# Empty loop footprints do not obstruct explicit nested-read transport
```c filename=probe.c
struct arena { int32 *data; int32 *occupied; int32 capacity; };
void fill(struct arena *arena, int32 start, int32 end) {
    int32 i = start;
    while (i < end) {
        arena->occupied[i] = 1;
        return;
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
            apply(separation::contains_subrange(p, 0, len, i, i + 1)) using {
                defined(i + 1); 0 <= i; i <= ((i + 1) as int32); ((i + 1) as int32) <= len;
            };
        }
        have separate(kept, memory(p[i..i + 1])) by {
            apply(separation::separate_restrict(whole, memory(p[0..len]), kept, memory(p[i..i + 1]))) using {
                defined(i + 1); separate(whole, memory(p[0..len])); contains(whole, kept);
                contains(memory(p[0..len]), memory(p[i..i + 1]));
            };
        }
        have contains(kept, kept) by { apply(click::separation::contains_refl(kept)) using {}; }
        have contains(memory(p[i..i + 1]), memory(p[i])) by {
            have i < ((i + 1) as int32) by solve() using { i <= 2147483646; };
            apply(separation::contains_element(p, i, i + 1, i)) using {
                defined(i + 1); i <= i; i < ((i + 1) as int32);
            };
        }
        apply(separation::separate_restrict(kept, memory(p[i..i + 1]), kept, memory(p[i]))) using {
            defined(i + 1); separate(kept, memory(p[i..i + 1])); contains(kept, kept);
            contains(memory(p[i..i + 1]), memory(p[i]));
        };
    }
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
    owns data[start..start];
    fact 0 <= start;
    fact start <= next;
    fact next <= end;
    fact end <= capacity;
    fact forall (k: int32) {
        next <= k and k < end implies occupied[k] == 0
    };
}

resource state(arena: struct arena*, start: int32, end: int32) {
    owns *arena;
    owns arena->occupied[0..arena->capacity];
    fact 0 <= start;
    fact start <= end;
    fact end <= arena->capacity;
    fact forall (k: int32) { start <= k and k < end implies arena->occupied[k] == 0 };
    fact separate(memory(*arena), memory(arena->data[0..arena->capacity]));
    fact separate(memory(*arena), memory(arena->occupied[0..arena->capacity]));
}
verifying "probe.c";
void fill(struct arena *arena, int32 start, int32 end) {
    consumes state(arena, start, end);
} by {
    unfold(state(arena, start, end));
    step(); step();
    let w = fold(arena_window(arena->data, arena->occupied, arena->capacity, start, end), { next: start });
    loop mark_free_run {
        decreases to_integer(end) - to_integer(i);
        owns w: arena_window(arena->data, arena->occupied, arena->capacity, start, end);
        invariant w.next == i;
        invariant arena->data == old(arena->data);
        invariant arena->occupied == old(arena->occupied);
        initialize by solve();
        maintain by {
            let { next: m } = unfold(w);
            have m == i;
            have i < end;
            have end <= arena->capacity;
            have 0 <= i;
            have i < arena->capacity;
            mark opened;
            have contains(memory(*arena), memory(arena->occupied)) by { normalize(); }
            have separate(memory(arena->occupied), memory(arena->occupied[i])) by {
                apply(selected_array_cell(memory(*arena), memory(arena->occupied),
                    arena->occupied, arena->capacity, i)) using {
                    separate(memory(*arena), memory(arena->occupied[0..arena->capacity]));
                    contains(memory(*arena), memory(arena->occupied));
                    0 <= i; i < arena->capacity;
                };
            }
            step();
            have separate(loop(0).statement(0).footprint, memory(arena->occupied)) by {
                solve() using {
                    at(opened, separate(memory(arena->occupied), memory(arena->occupied[i])));
                };
            }
            have arena->occupied == at(opened, arena->occupied) by {
                preserve(memory(arena->occupied), loop(0).statement(0));
            }
            have arena->occupied == old(arena->occupied) by {
                solve() using {
                    arena->occupied == at(opened, arena->occupied);
                    at(opened, arena->occupied) == old(arena->occupied);
                };
            }
            have forall (k: int32) {
                at(opened, i) < k and k < end implies
                    arena->occupied[k] == 0
            } by {
                intro();
                intro();
                have at(opened, i) < k;
                have k < end;
                have at(opened, i) <= k;
                have m <= k;
                have at(opened, arena->occupied[k]) == 0 by {
                    have at(opened, m) <= at(opened, k) and
                            at(opened, k) < at(opened, end);
                    instantiate(forall (j: int32) {
                        at(opened, m) <= at(opened, j) and
                            at(opened, j) < at(opened, end) implies
                            at(opened, arena->occupied[j]) == at(opened, 0)
                    }, k);
                    known();
                }
                have 0 <= k;
                have k < at(opened, arena->capacity);
                have at(opened, i) != k by { solve() using { at(opened, i) < k; }; }
                have at(opened, separate(memory(arena->occupied[i]), memory(arena->occupied[k]))) by {
                    apply(separation::separate_elements(at(opened, arena->occupied), at(opened, i), k)) using { at(opened, i) != k; };
                }
                have arena->occupied == at(opened, arena->occupied) by { known(); }
                // Select the preserved cell as one complete int32 observation.
                have contains(at(opened, memory(arena->occupied[k])), at(opened, memory((&arena->occupied[k])[0..1]))) by { normalize(); }
                have contains(at(opened, memory(arena->occupied[i])), at(opened, memory(arena->occupied[i]))) by { transport(at(function.entry, contains(at(opened, memory(load<int32*>(byte_offset(arena, 8))[i])), at(opened, memory(load<int32*>(byte_offset(arena, 8))[i])))), contains(at(opened, memory(load<int32*>(byte_offset(arena, 8))[i])), at(opened, memory(load<int32*>(byte_offset(arena, 8))[i])))) using {
                    }; }
                have separate(at(opened, memory(arena->occupied[i])), at(opened, memory((&arena->occupied[k])[0..1]))) by {
                    apply(separation::separate_restrict(at(opened, memory(arena->occupied[i])), at(opened, memory(arena->occupied[k])), at(opened, memory(arena->occupied[i])), at(opened, memory((&arena->occupied[k])[0..1])))) using {
                        contains(at(opened, memory(arena->occupied[i])), at(opened, memory(arena->occupied[i])));
                        at(opened, separate(memory(arena->occupied[i]), memory(arena->occupied[k])));
                        contains(at(opened, memory(arena->occupied[k])), at(opened, memory((&arena->occupied[k])[0..1])));
                    };
                }
                have separate(loop(0).statement(0).footprint, at(opened, memory((&arena->occupied[k])[0..1]))) by {
                    known();
                }
                have at(loop(0).statement(0).exit, load<int32>(at(opened, &arena->occupied[k])))
                        == at(loop(0).statement(0).entry, load<int32>(at(opened, &arena->occupied[k]))) by {
                    preserve(at(opened, memory((&arena->occupied[k])[0..1])), loop(0).statement(0));
                }
                have arena->occupied[k] == at(opened, arena->occupied[k]) by {
                    rewrite(arena->occupied, at(opened, arena->occupied));
                    known();
                }
                known();
            }
            step();
        }
    }
}
```
```expect
pass
```
