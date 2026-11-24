# Naming a resource cell preserves an ordinary field read

Unfolding the nested resource names a cell in the external object. The
local field keeps its recorded write across that naming and the sibling store.

```c filename=fields.c
struct Pair {
    int32 left;
    int32 right;
};

int32 read_right(int32 value, int32* external) {
    struct Pair pair;
    pair.right = value;
    pair.left = 1;
    return pair.right;
}
```

```click
resource cell(p: int32*) {
    owns p[0..1];
}
resource wrapped(p: int32*) {
    owns cell(p);
}
verifying "fields.c";

int32 read_right(int32 value, int32* external) {
    owns wrapped(external);
    ensures result == value;
} by {
    step_until(statement(2).entry);
    mark written;
    unfold(wrapped(external));
    unfold(cell(external));
    mark named;
    step();
    have pair.right == value by solve();
    have separate(memory(pair.left), memory(pair.right)) by known();
    have separate(statement(2).footprint, memory(pair.right)) by {
        close() using { separate(memory(pair.left), memory(pair.right)); };
    }
    have pair.right == at(written, pair.right) by {
        preserve(memory(pair.right), statement(2));
    }
    fold(cell(external));
    fold(wrapped(external));
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
