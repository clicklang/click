# An ordinary read keeps its field's write across a sibling store

The two fields occupy disjoint byte ranges in the same automatic object.

```c filename=fields.c
struct Pair {
    int32 left;
    int32 right;
};

int32 read_right(int32 value) {
    struct Pair pair;
    pair.right = value;
    pair.left = 1;
    return pair.right;
}
```

```click
verifying "fields.c";

int32 read_right(int32 value) {
    ensures result == value;
} by {
    step_until(statement(2).entry);
    mark written;
    step();
    have pair.right == value by close();
    have separate(memory(pair.left), memory(pair.right)) by close();
    have separate(statement(2).footprint, memory(pair.right)) by {
        close() using { separate(memory(pair.left), memory(pair.right)); };
    }
    have pair.right == at(written, pair.right) by {
        preserve(memory(pair.right), statement(2));
    }
    step_until(function.exit);
    close();
}
```

```expect
pass
```
