# A loop frame keeps two header cells of a map reached through a field

`mark_tail` marks `arena->occupied[i]` from index 2 up to `end`, leaving
the two header cells `arena->occupied[0]` and `arena->occupied[1]` alone;
the loop's bound check reads the map's length through the `capacity` field.
One invariant per header cell says it keeps its entry value. The proof names
the saved map pointer and both complete cells, then carries those reads over
the store and the index increment. Expansion must recheck both invariants,
including the second cell at a displacement from the saved pointer.

```c filename=loop_frame_keeps_two_header_cells_of_a_field_map.c
struct arena {
    int32* occupied;
    int32 capacity;
};

void mark_tail(struct arena* arena, int32 end) {
    int32 i;
    i = 2;
    while (i < end) {
        arena->occupied[i] = 1;
        i = i + 1;
    }
}
```

```click
verifying "loop_frame_keeps_two_header_cells_of_a_field_map.c";

void mark_tail(struct arena* arena, int32 end) {
    owns *arena;
    owns arena->occupied[0..arena->capacity];
    requires separate(
        memory(*arena),
        memory(arena->occupied[0..arena->capacity])
    );
    requires 2 <= end;
    requires end <= arena->capacity;
} by {
    step();
    step();
    loop {
        owns arena->occupied[0..arena->capacity];
        invariant 2 <= i;
        invariant i <= end;
        invariant arena->occupied[0] == old(arena->occupied[0]);
        invariant arena->occupied[1] == old(arena->occupied[1]);
        decreases end - i;
        initialize by solve();
        maintain by {
            mark iteration;
            have i != 0 by { solve() using { 2 <= i; }; }
            have i != 1 by { solve() using { 2 <= i; }; }
            have separate(memory(arena->occupied[i]), memory(arena->occupied[0])) by {
                apply(click::separation::separate_elements(arena->occupied, i, 0));
            }
            have separate(memory(arena->occupied[i]), memory(arena->occupied[1])) by {
                apply(click::separation::separate_elements(arena->occupied, i, 1));
            }
            have contains(memory(*arena), memory(arena->occupied)) by normalize();
            apply(click::separation::contains_element(arena->occupied, 0, arena->capacity, i));
            have separate(memory(arena->occupied[i]), memory(arena->occupied)) by {
                apply(click::separation::separate_restrict(memory(arena->occupied[0..arena->capacity]), memory(*arena), memory(arena->occupied[i]), memory(arena->occupied)));
            }
            step();
            have separate(loop(0).statement(0).footprint, at(iteration, memory((&arena->occupied[0])[0..1]))) by {
                normalize() using { at(iteration, separate(memory(arena->occupied[i]), memory(arena->occupied[0]))); };
            }
            have separate(loop(0).statement(0).footprint, memory(arena->occupied)) by {
                normalize() using { at(iteration, separate(memory(arena->occupied[i]), memory(arena->occupied))); };
            }
            have arena->occupied == at(loop(0).statement(0).entry, arena->occupied) by {
                preserve(memory(arena->occupied), loop(0).statement(0));
            }
            have at(loop(0).statement(0).exit, load<int32>(at(iteration, &arena->occupied[0])))
                    == at(loop(0).statement(0).entry, load<int32>(at(iteration, &arena->occupied[0]))) by {
                preserve(at(iteration, memory((&arena->occupied[0])[0..1])), loop(0).statement(0));
            }
            have arena->occupied[0] == at(loop(0).statement(0).entry, arena->occupied[0]) by {
                rewrite(arena->occupied, at(iteration, arena->occupied));
                known();
            }
            have separate(loop(0).statement(0).footprint, at(iteration, memory((&arena->occupied[1])[0..1]))) by {
                normalize() using { at(iteration, separate(memory(arena->occupied[i]), memory(arena->occupied[1]))); };
            }
            have at(loop(0).statement(0).exit, load<int32>(at(iteration, &arena->occupied[1])))
                    == at(loop(0).statement(0).entry, load<int32>(at(iteration, &arena->occupied[1]))) by {
                preserve(at(iteration, memory((&arena->occupied[1])[0..1])), loop(0).statement(0));
            }
            have arena->occupied[1] == at(loop(0).statement(0).entry, arena->occupied[1]) by {
                rewrite(arena->occupied, at(iteration, arena->occupied));
                known();
            }
            step();
            have separate(loop(0).statement(1).footprint, at(iteration, memory((&arena->occupied[0])[0..1]))) by {
                known();
            }
            have separate(loop(0).statement(1).footprint, memory(arena->occupied)) by {
                known();
            }
            have arena->occupied == at(loop(0).statement(1).entry, arena->occupied) by {
                preserve(memory(arena->occupied), loop(0).statement(1));
            }
            have arena->occupied == at(iteration, arena->occupied) by known();
            have at(loop(0).statement(1).exit, load<int32>(at(iteration, &arena->occupied[0])))
                    == at(loop(0).statement(1).entry, load<int32>(at(iteration, &arena->occupied[0]))) by {
                preserve(at(iteration, memory((&arena->occupied[0])[0..1])), loop(0).statement(1));
            }
            have arena->occupied[0] == at(loop(0).statement(1).entry, arena->occupied[0]) by {
                rewrite(arena->occupied, at(iteration, arena->occupied));
                known();
            }
            have separate(loop(0).statement(1).footprint, at(iteration, memory((&arena->occupied[1])[0..1]))) by {
                known();
            }
            have at(loop(0).statement(1).exit, load<int32>(at(iteration, &arena->occupied[1])))
                    == at(loop(0).statement(1).entry, load<int32>(at(iteration, &arena->occupied[1]))) by {
                preserve(at(iteration, memory((&arena->occupied[1])[0..1])), loop(0).statement(1));
            }
            have arena->occupied[1] == at(loop(0).statement(1).entry, arena->occupied[1]) by {
                rewrite(arena->occupied, at(iteration, arena->occupied));
                known();
            }
            have arena->occupied[0] == old(arena->occupied[0]) by {
                rewrite(arena->occupied[0], at(loop(0).statement(1).entry, arena->occupied[0]));
                rewrite(at(loop(0).statement(1).entry, arena->occupied[0]), at(iteration, arena->occupied[0]));
                known();
            }
            have arena->occupied[1] == old(arena->occupied[1]) by {
                rewrite(arena->occupied[1], at(loop(0).statement(1).entry, arena->occupied[1]));
                rewrite(at(loop(0).statement(1).entry, arena->occupied[1]), at(iteration, arena->occupied[1]));
                known();
            }
        }
    }
}
```

```expect
pass
```
