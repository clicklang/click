# A fold rejoins a constant range at a symbolic split

The two resources keep `x[0..split]` and `x[split..4]` apart until the proof
unfolds them. Their endpoints meet at `split`, so folding the whole range
consumes both pieces.

```c filename=two_pieces.c
void rejoin(int32* x, int32 split) {}
```

```click
verifying "two_pieces.c";

resource first(x: int32*, split: int32) { owns x[0..split]; }
resource last(x: int32*, split: int32) { owns x[split..4]; }
resource whole(x: int32*) { owns x[0..4]; }

void rejoin(int32* x, int32 split) {
    requires 0 <= split;
    requires split < 4;
    consumes first(x, split);
    consumes last(x, split);
    produces x[0..4];
} by {
    unfold(first(x, split));
    unfold(last(x, split));
    fold(whole(x));
    unfold(whole(x));
    step();
}
```

```expect
pass
```
