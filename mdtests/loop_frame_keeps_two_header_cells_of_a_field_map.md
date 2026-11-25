# A loop frame keeps two header cells of a map reached through a field

`mark_tail` marks `arena->occupied[i]` from index 2 up to `end`, leaving
the two header cells `arena->occupied[0]` and `arena->occupied[1]` alone;
the loop's bound check reads the map's length through the `capacity` field.
The back edge proves that the store is separate from the arena metadata
and both header cells. It carries the array pointer and each header value
across the same footprint, including the cell at index 1.

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
        initialize by close();
        maintain by {
            mark before_store;
            have i != 0 by { normalize() using { 2 <= i; }; }
            have i != 1 by { normalize() using { 2 <= i; }; }
            apply(click::separation::separate_elements(arena->occupied, i, 0));
            apply(click::separation::separate_elements(arena->occupied, i, 1));
            have contains(memory(arena->occupied[0..arena->capacity]), memory(arena->occupied[i])) by {
                have i < arena->capacity by {
                    apply(click::integer::int32_less_than_less_equal_transitive(i, end, arena->capacity));
                }
                apply(click::separation::contains_element(arena->occupied, 0, arena->capacity, i));
            }
            apply(click::separation::contains_refl(memory(*arena)));
            apply(click::separation::separate_restrict(
                memory(*arena), memory(arena->occupied[0..arena->capacity]),
                memory(*arena), memory(arena->occupied[i])));
            step();
            have separate(loop(0).statement(0).footprint, at(before_store, memory(*arena))) by {
                normalize() using {
                    at(before_store, separate(memory(*arena), memory(arena->occupied[i])));
                };
            }
            apply(click::separation::contains_refl(loop(0).statement(0).footprint));
            have contains(at(before_store, memory(*arena)), at(before_store, memory(arena->occupied))) by {
                normalize();
            }
            apply(click::separation::separate_restrict(
                loop(0).statement(0).footprint, at(before_store, memory(*arena)),
                loop(0).statement(0).footprint, at(before_store, memory(arena->occupied))));
            have arena->occupied == at(before_store, arena->occupied) by {
                preserve(at(before_store, memory(arena->occupied)), loop(0).statement(0));
            }
            have separate(loop(0).statement(0).footprint, at(before_store, memory(arena->occupied[0]))) by {
                normalize() using {
                    at(before_store, separate(memory(arena->occupied[i]), memory(arena->occupied[0])));
                };
            }
            have load<int32>(at(before_store, &arena->occupied[0])) == at(before_store, arena->occupied[0]) by {
                preserve(at(before_store, memory(arena->occupied[0])), loop(0).statement(0));
            }
            have arena->occupied[0] == old(arena->occupied[0]) by {
                rewrite(arena->occupied, at(before_store, arena->occupied));
                close();
            }
            have separate(loop(0).statement(0).footprint, at(before_store, memory(arena->occupied[1]))) by {
                normalize() using {
                    at(before_store, separate(memory(arena->occupied[i]), memory(arena->occupied[1])));
                };
            }
            have load<int32>(at(before_store, &arena->occupied[1])) == at(before_store, arena->occupied[1]) by {
                preserve(at(before_store, memory(arena->occupied[1])), loop(0).statement(0));
            }
            have arena->occupied[1] == old(arena->occupied[1]) by {
                rewrite(arena->occupied, at(before_store, arena->occupied));
                close();
            }
            step();
            close();
        }
    }
}
```

```expect
pass
```
