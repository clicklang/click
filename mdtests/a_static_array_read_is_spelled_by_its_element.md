# A static array read is spelled by its element

A read of a function-local `static` array keeps its version name, so a smart
step that cites the entry value of an element needs that read spelled
(`docs/internals/spellability.md`). The speller writes an element of a
`static` scalar array by its source name and declared subscripts,
`old(batches[0][0])`, and a field of a `static` struct array as a typed read
at the element's address. The closing `auto` here cites the entry reads in an
`Integer` refutation: `result` is the sum the C code computed from the stored
values, `old(calls) + 1` and `old(grid[0][0]) + 1`, while the `have` names the
reads at the final state, and only spelled entry reads connect the two. This
is `examples/multifile-registry`'s pattern.

```c filename=static_reads.c
struct counter {
    int32 value;
    int32 name;
};

static int32 calls = 0;

int32 bump_grid() {
    static int32 grid[][2] = {{0, 7}};
    calls = calls + 1;
    grid[0][0] = grid[0][0] + 1;
    return calls + grid[0][0];
}

int32 bump_counter() {
    static struct counter counters[] = {{0, 98}};
    calls = calls + 1;
    counters[0].value = counters[0].value + 1;
    return calls + counters[0].value;
}
```

```click
verifying "static_reads.c";

int32 bump_grid() {
    requires calls > -1000;
    requires calls < 1000;
    requires grid[0][0] > -1000;
    requires grid[0][0] < 1000;
    owns calls;
    owns grid[0..2];
    ensures calls == old(calls) + 1;
    ensures grid[0][0] == old(grid[0][0]) + 1;
    ensures result == old(calls) + old(grid[0][0]) + 2;
} by {
    step_until(function.exit);
    have to_integer(calls + grid[0][0]) == to_integer(calls) + to_integer(grid[0][0]) by auto();
    auto();
}

int32 bump_counter() {
    requires calls > -1000;
    requires calls < 1000;
    requires counters[0].value > -1000;
    requires counters[0].value < 1000;
    owns calls;
    owns counters[0].value;
    ensures calls == old(calls) + 1;
    ensures counters[0].value == old(counters[0].value) + 1;
    ensures result == old(calls) + old(counters[0].value) + 2;
} by {
    step_until(function.exit);
    have to_integer(calls + counters[0].value) == to_integer(calls) + to_integer(counters[0].value) by auto();
    auto();
}
```

```expect
pass
```
