# A call footprint must not treat ownership rejoining as a memory write

```c filename=call_frame.c
struct box { unsigned long tag; int *data; };
void update(struct box *q) { q->tag = 1; }
void caller(struct box *q) { update(q); }
```

```click
verifying "call_frame.c";
void update(struct box *q) { owns q->tag; } by { step(); step(); solve(); }
void caller(struct box *q) {
    owns *q;
    ensures q->data == old(q->data);
} by {
    have separate(memory(q->tag), memory(q->data));
    mark before;
    step();
    have separate(statement(0).footprint, memory(q->data)) by {
        normalize() using { separate(memory(q->tag), memory(q->data)); };
    }
    have q->data == at(before, q->data) by {
        transport_certificate {
            premise 0: separate(statement(0).footprint, memory(q->data))
                => separate(statement(0).footprint, memory(q->data));
            preserve 0 => q->data == at(before, q->data);
            conclusion 1;
        }
    }
    step();
    assumption();
}
```

```expect
pass
```
