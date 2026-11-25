# Return descriptor-backed elements to iterated ownership across a loop

The occupied-cell store makes the guard true. indexed `fold` returns the corresponding
owned suffix element through a fresh descriptor read. Keep the descriptor
access and loop: a single-store control does not reproduce the recovery bug.
The explicit field and separation facts support the later window fold.
Select the whole descriptor view for partition separation, then restrict it
to the fields; the individual field spellings need not be independent held
resources. Preserve the untouched occupancy cells across the store and increment.

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
        have i <= 2147483646 by { close() using { i < len; }; }
        have defined(i + 1) by { close() using { 0 <= i; i <= 2147483646; }; }
        have i <= ((i + 1) as int32) by { close() using { 0 <= i; i < len; }; }
        have ((i + 1) as int32) <= len by { close() using { 0 <= i; i < len; }; }
        have contains(memory(p[0..len]), memory(p[i..i + 1])) by {
            apply(separation::contains_subrange(p, 0, len, i, i + 1));
        }
        have separate(kept, memory(p[i..i + 1])) by {
            apply(separation::separate_restrict(whole, memory(p[0..len]), kept, memory(p[i..i + 1])));
        }
        have contains(kept, kept) by { apply(click::separation::contains_refl(kept)); }
        have contains(memory(p[i..i + 1]), memory(p[i])) by {
            have i < ((i + 1) as int32) by close() using { i <= 2147483646; };
            apply(separation::contains_element(p, i, i + 1, i));
        }
        apply(separation::separate_restrict(kept, memory(p[i..i + 1]), kept, memory(p[i])));
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
    requires separate(memory(arena->data[0..arena->capacity]), memory(*arena));
    consumes w: arena_clear_window(arena->data, arena->occupied, arena->capacity, start, end);
    requires w.next == start;
    requires arena->capacity <= 536870911;
    produces arena_cells(arena->data, arena->occupied, arena->capacity);
} by {
    let { next: initial_next } = unfold(w);
    have 0 <= arena->capacity by { close(); }
    have separate(memory(arena->occupied[0..arena->capacity]), memory(*arena)) by { close(); }
    have contains(memory(arena->occupied[0..arena->capacity]), memory(arena->occupied[0..arena->capacity])) by { apply(click::separation::contains_refl(memory(arena->occupied[0..arena->capacity]))); }
    have contains(memory(*arena), memory(arena->data)) by { close(); }
    have separate(memory(arena->occupied[0..arena->capacity]), memory(arena->data)) by {
        apply(separation::separate_restrict(memory(arena->occupied[0..arena->capacity]), memory(*arena), memory(arena->occupied[0..arena->capacity]), memory(arena->data)));
    }
    have contains(memory(*arena), memory(arena->occupied)) by { close(); }
    have separate(memory(arena->occupied[0..arena->capacity]), memory(arena->occupied)) by {
        apply(separation::separate_restrict(memory(arena->occupied[0..arena->capacity]), memory(*arena), memory(arena->occupied[0..arena->capacity]), memory(arena->occupied)));
    }
    have contains(memory(*arena), memory(arena->capacity)) by { close(); }
    have separate(memory(arena->occupied[0..arena->capacity]), memory(arena->capacity)) by {
        apply(separation::separate_restrict(memory(arena->occupied[0..arena->capacity]), memory(*arena), memory(arena->occupied[0..arena->capacity]), memory(arena->capacity)));
    }
    have 0 <= initial_next by { close(); }
    have contains(memory(arena->data[0..arena->capacity]), memory(arena->data[initial_next..end])) by {
        apply(separation::contains_subrange(arena->data, 0, arena->capacity, initial_next, end));
    }
    have contains(memory(*arena), memory(*arena)) by { apply(click::separation::contains_refl(memory(*arena))); }
    have separate(memory(arena->data[initial_next..end]), memory(*arena)) by {
        apply(separation::separate_restrict(memory(arena->data[0..arena->capacity]), memory(*arena), memory(arena->data[initial_next..end]), memory(*arena)));
    }
    let w = fold(arena_clear_window(arena->data, arena->occupied, arena->capacity, start, end), { next: initial_next });
    step(); step();
    loop clear_occupied {
        decreases end - i;
        owns w: arena_clear_window(arena->data, arena->occupied, arena->capacity, start, end);
        invariant w.next == i;
        invariant separate(memory(arena->occupied[0..arena->capacity]), memory(*arena));
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
        initialize by close();
        maintain by {
            let { next: m } = unfold(w);
            have m == i;
            have 0 <= start;
            have start <= m;
            have start <= i;
            have 0 <= i;
            have end <= arena->capacity;
            have i < arena->capacity;
            have 0 < arena->capacity by { close(); }
            have separate(memory(arena->occupied[0..arena->capacity]), memory(arena->data)) by { close(); }
            have separate(memory(arena->occupied[i]), memory(arena->data)) by {
                apply(separation::separate_symm(memory(arena->occupied[0..arena->capacity]), memory(arena->data)));
                apply(separation::contains_refl(memory(arena->data)));
                apply(selected_array_cell(memory(arena->data), memory(arena->data), arena->occupied, arena->capacity, i));
                apply(separation::separate_symm(memory(arena->data), memory(arena->occupied[i])));
            }
            have separate(memory(arena->occupied[i]), memory(arena->occupied)) by {
                apply(separation::separate_symm(memory(arena->occupied[0..arena->capacity]), memory(arena->occupied)));
                apply(separation::contains_refl(memory(arena->occupied)));
                apply(selected_array_cell(memory(arena->occupied), memory(arena->occupied), arena->occupied, arena->capacity, i));
                apply(separation::separate_symm(memory(arena->occupied), memory(arena->occupied[i])));
            }
            have separate(memory(arena->occupied[i]), memory(arena->capacity)) by {
                apply(separation::separate_symm(memory(arena->occupied[0..arena->capacity]), memory(arena->capacity)));
                apply(separation::contains_refl(memory(arena->capacity)));
                apply(selected_array_cell(memory(arena->capacity), memory(arena->capacity), arena->occupied, arena->capacity, i));
                apply(separation::separate_symm(memory(arena->capacity), memory(arena->occupied[i])));
            }
            have contains(memory(arena->occupied[0..arena->capacity]), memory(arena->occupied[i])) by {
                apply(separation::contains_element(arena->occupied, 0, arena->capacity, i));
            }
            have contains(memory(*arena), memory(*arena)) by { close(); }
            have separate(memory(arena->occupied[i]), memory(*arena)) by {
                apply(separation::separate_restrict(memory(arena->occupied[0..arena->capacity]), memory(*arena), memory(arena->occupied[i]), memory(*arena)));
            }
            mark opened;
            step();
            have at(opened, separate(loop(0).statement(0).footprint, memory(arena->data))) by {
                close();
            }
            have arena->data == at(opened, arena->data) by {
                preserve(at(opened, memory(arena->data)), loop(0).statement(0));
            }
            have at(opened, separate(loop(0).statement(0).footprint, memory(arena->occupied))) by {
                close();
            }
            have arena->occupied == at(opened, arena->occupied) by {
                preserve(at(opened, memory(arena->occupied)), loop(0).statement(0));
            }
            have at(opened, separate(loop(0).statement(0).footprint, memory(arena->capacity))) by {
                close();
            }
            have arena->capacity == at(opened, arena->capacity) by { close(); }
            fold(at(opened, arena_clear_window(arena->data, arena->occupied, arena->capacity, start, end))[i]);
            step();
            have to_integer(start) <= to_integer(at(opened, i) + 1);
            have forall (k: int32) {
                start <= k and to_integer(k) < to_integer(at(opened, i) + 1) implies arena->occupied[k] == 0
            } by {
                intro() {
                    intro() {
                        have start <= k;
                        have to_integer(k) < to_integer(at(opened, i) + 1);
                        if k < at(opened, i) {
                            have k < m;
                            have at(opened, arena->occupied[k]) == 0 by {
                                have at(opened, start) <= at(opened, k) and
                                        at(opened, k) < at(opened, m);
                                instantiate(forall (j: int32) {
                                    at(opened, start) <= at(opened, j) and
                                        at(opened, j) < at(opened, m) implies
                                        at(opened, arena->occupied[j]) == at(opened, 0)
                                }, k);
                                close();
                            }
                            have 0 <= k;
                            have at(opened, i) != k by { close() using { k < at(opened, i); }; }
                            have at(opened, separate(memory(arena->occupied[i]), memory(arena->occupied[k]))) by {
                                apply(separation::separate_elements(at(opened, arena->occupied), at(opened, i), k));
                            }
                            have at(opened, separate(loop(0).statement(0).footprint, memory(arena->occupied[k]))) by {
                                close();
                            }
                            have at(loop(0).statement(0).exit, arena->occupied[k]) == at(opened, arena->occupied[k]) by {
                                preserve(at(opened, memory(arena->occupied[k])), loop(0).statement(0));
                            }
                            have separate(loop(0).statement(1).footprint, memory(arena->occupied[k])) by {
                                close() using {};
                            }
                            have arena->occupied[k] == at(loop(0).statement(1).entry, arena->occupied[k]) by {
                                preserve(memory(arena->occupied[k]), loop(0).statement(1));
                            }
                            close();
                        } else {
                            have k <= at(opened, i);
                            have k == at(opened, i);
                            rewrite(k, at(opened, i));
                            close();
                        }
                    }
                }
            }
            have forall (k: int32) {
                0 <= k and k < start implies
                    arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k])
            } by {
                intro() {
                    intro() {
                        have 0 <= k;
                        have k < start;
                        have at(opened, arena->occupied[k]) ==
                            at(clear_occupied.entry, arena->occupied[k]) by {
                            have at(opened, 0) <= at(opened, k) and
                                    at(opened, k) < at(opened, start);
                            instantiate(forall (j: int32) {
                                at(opened, 0) <= at(opened, j) and
                                    at(opened, j) < at(opened, start) implies
                                    at(opened, arena->occupied[j]) ==
                                        at(clear_occupied.entry, arena->occupied[j])
                            }, k);
                            close();
                        }
                        have k < at(opened, i);
                        have at(opened, i) != k by { close() using { k < at(opened, i); }; }
                        have at(opened, separate(memory(arena->occupied[i]), memory(arena->occupied[k]))) by {
                            apply(separation::separate_elements(at(opened, arena->occupied), at(opened, i), k));
                        }
                        have at(opened, separate(loop(0).statement(0).footprint, memory(arena->occupied[k]))) by {
                            close();
                        }
                        have at(loop(0).statement(0).exit, arena->occupied[k]) == at(opened, arena->occupied[k]) by {
                            preserve(at(opened, memory(arena->occupied[k])), loop(0).statement(0));
                        }
                        have separate(loop(0).statement(1).footprint, memory(arena->occupied[k])) by {
                            close() using {};
                        }
                        have arena->occupied[k] == at(loop(0).statement(1).entry, arena->occupied[k]) by {
                            preserve(memory(arena->occupied[k]), loop(0).statement(1));
                        }
                        close();
                    }
                }
            }
            have forall (k: int32) {
                end <= k and k < arena->capacity implies
                    arena->occupied[k] == at(clear_occupied.entry, arena->occupied[k])
            } by {
                intro() {
                    intro() {
                        have end <= k;
                        have k < arena->capacity;
                        have at(opened, arena->occupied[k]) ==
                            at(clear_occupied.entry, arena->occupied[k]) by {
                            have at(opened, end) <= at(opened, k) and
                                    at(opened, k) < at(opened, arena->capacity);
                            instantiate(forall (j: int32) {
                                at(opened, end) <= at(opened, j) and
                                    at(opened, j) < at(opened, arena->capacity) implies
                                    at(opened, arena->occupied[j]) ==
                                        at(clear_occupied.entry, arena->occupied[j])
                            }, k);
                            close();
                        }
                        have at(opened, i) < k;
                        have at(opened, i) <= k;
                        have 0 <= k;
                        have at(opened, i) != k by { close() using { at(opened, i) < k; }; }
                        have at(opened, separate(memory(arena->occupied[i]), memory(arena->occupied[k]))) by {
                            apply(separation::separate_elements(at(opened, arena->occupied), at(opened, i), k));
                        }
                        have at(opened, separate(loop(0).statement(0).footprint, memory(arena->occupied[k]))) by {
                            close();
                        }
                        have at(loop(0).statement(0).exit, arena->occupied[k]) == at(opened, arena->occupied[k]) by {
                            preserve(at(opened, memory(arena->occupied[k])), loop(0).statement(0));
                        }
                        have separate(loop(0).statement(1).footprint, memory(arena->occupied[k])) by {
                            close() using {};
                        }
                        have arena->occupied[k] == at(loop(0).statement(1).entry, arena->occupied[k]) by {
                            preserve(memory(arena->occupied[k]), loop(0).statement(1));
                        }
                        close();
                    }
                }
            }
            have arena->data == old(arena->data);
            have arena->occupied == old(arena->occupied);
            have arena->capacity == old(arena->capacity);
            have separate(memory(arena->occupied[0..arena->capacity]), memory(arena->data[0..arena->capacity])) by {
                rewrite(arena->data, old(arena->data));
                rewrite(arena->occupied, old(arena->occupied));
                rewrite(arena->capacity, old(arena->capacity));
                close();
            }
            let w = fold(arena_clear_window(old(arena->data), old(arena->occupied), old(arena->capacity), start, end), {
                next: at(opened, i) + 1
            });
            have start <= end;
        }
    }
    let { next: n } = unfold(w);
    have n <= end;
    have n == i;
    have not (n < end) by { rewrite(n, i); close(); }
    have n == end;
    step_until(function.exit);
    have arena->data == old(arena->data);
    have arena->occupied == old(arena->occupied);
    have arena->capacity == old(arena->capacity);
    fold(arena_cells(old(arena->data), old(arena->occupied), old(arena->capacity)));
    close();
}
```

```expect
pass
```
