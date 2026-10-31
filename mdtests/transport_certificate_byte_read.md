# A transport certificate preserves a separated byte read

```c filename=keep.c
void keep(unsigned char *p, unsigned char *q) { *p = 0; }
```

```click
verifying "keep.c";
void keep(uint8* p, uint8* q) {
    owns *p;
    views *q;
    requires separate(memory(*p), memory(*q));
} by {
    step();
    have separate(statement(0).footprint, memory(*q)) by {
        normalize() using { separate(memory(*p), memory(*q)); };
    }
    have *q == at(statement(0).entry, *q) by {
        transport_certificate {
            premise 0: separate(statement(0).footprint, memory(*q))
                => separate(statement(0).footprint, memory(*q));
            preserve 0 => *q == at(statement(0).entry, *q);
            conclusion 1;
        }
    }
    step_until(function.exit);
}
```

```expect
pass
```
