# Copy a word while retaining its explicit pointer relationship

Preserve the complete eight-byte observation through a pointer-typed view.
A numeric word equality alone does not connect the casts' provenance. The
certificate crosses the local declaration; assignment then copies that value.

```c filename=saved.c
void copy(unsigned long* slot, int32* p) {
    unsigned long saved = *slot;
}
```

```click
verifying "saved.c";
void copy(unsigned long* slot, int32* p) {
    views *slot;
    requires ((*slot & ~1) as (int32 *)) == p;
} by {
    mark before;
    step();
    have separate(statement(0).region(0).footprint, memory(*slot)) by {
        normalize() using {};
    }
    have *(slot as (int32 **)) == at(before, *(slot as (int32 **))) by {
        transport_certificate {
            premise 0: separate(statement(0).region(0).footprint, memory(*slot))
                => separate(statement(0).region(0).footprint, memory(*slot));
            preserve 0 => *(slot as (int32 **)) == at(before, *(slot as (int32 **)));
            conclusion 1;
        }
    }
    have ((*slot & ~1) as (int32 *)) == p by {
        assumption();
    }
    step();
    have ((saved & ~1) as (int32 *)) == p by { assumption(); }
}
```

```expect
pass
```
