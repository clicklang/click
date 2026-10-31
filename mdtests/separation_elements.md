# Unequal array indices separate complete elements

```c filename=keep.c
void keep(unsigned char *bytes, unsigned long i, unsigned long k) { bytes[i] = 0; }
```

```click
import click::separation;
verifying "keep.c";
void keep(uint8* bytes, uint64 i, uint64 k) {
    owns bytes[0..4];
    requires 0 <= k and k < i and i < 4;
} by {
    have separate(memory(*(bytes + i)), memory(*(bytes + k))) by {
        have i != k by { solve() using { k < i; }; }
        apply(separation::elements(bytes, i, k)) using { i != k; };
    }
    mark before;
    step();
    have separate(statement(0).footprint, memory(*(bytes + k))) by {
        normalize() using { separate(memory(*(bytes + i)), memory(*(bytes + k))); };
    }
    have bytes[k] == at(before, bytes[k]) by {
        transport_certificate {
            premise 0: separate(statement(0).footprint, memory(*(bytes + k)))
                => separate(statement(0).footprint, memory(*(bytes + k)));
            preserve 0 => bytes[k] == at(before, bytes[k]);
            conclusion 1;
        }
    }
    step_until(function.exit);
}
```

```expect
pass
```
