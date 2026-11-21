# Explicit comparison transport inside a C proof's `have`

The entry comparison reads `next[0]`. A store to a separate array cannot
change that read, so the same comparison holds at the post-store frontier.

```c filename=comparison_fact_explicit_transport_inside_have.c
void mark(int32 *next, int32 *visited) {
    visited[0] = 1;
}
```

```click
verifying "comparison_fact_explicit_transport_inside_have.c";

void mark(int32 *next, int32 *visited) {
    views next[0..1];
    owns visited[0..1];
    requires separate(memory(next[0..1]), memory(visited[0..1]));
    requires 0 <= next[0];
    ensures 0 <= next[0];
} by {
    mark entry;
    have at(entry, 0 <= next[0]) by known();
    have contains(memory(next[0..1]), memory(next[0])) by { apply(click::separation::contains_element(next, 0, 1, 0)) using { 0 <= 0; 0 < 1; }; }
    have contains(memory(visited[0..1]), memory(visited[0])) by { apply(click::separation::contains_element(visited, 0, 1, 0)) using { 0 <= 0; 0 < 1; }; }
    have separate(memory(next[0]), memory(visited[0])) by {
        apply(click::separation::separate_restrict(memory(next[0..1]), memory(visited[0..1]), memory(next[0]), memory(visited[0]))) using {
            separate(memory(next[0..1]), memory(visited[0..1]));
            contains(memory(next[0..1]), memory(next[0]));
            contains(memory(visited[0..1]), memory(visited[0]));
        };
    }
    step();
    have separate(statement(0).footprint, memory(next[0])) by {
        solve() using { separate(memory(next[0]), memory(visited[0])); };
    }
    have next[0] == at(entry, next[0]) by {
        preserve(memory(next[0]), statement(0));
    }
    have 0 <= next[0] by {
        known();
    }
}
```

```expect
pass
```
