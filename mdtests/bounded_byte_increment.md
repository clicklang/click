# A bounded byte increment retains both signed and unsigned bounds

A byte widened to a word retains its width bound, but a stronger signed
precondition must still tighten that bound. Constant operands may already
be folded to int64 constants in the widened overflow obligation.

```c filename=bounded_byte_increment.c
long next(unsigned char byte) {
    unsigned word = (unsigned)byte;
    return (long)word + 1;
}
```

```click
verifying "bounded_byte_increment.c";
int64 next(uint8 byte) {
    requires byte < 255;
    ensures result <= 255i64;
} by {
    execute();
    have result <= 255i64 by {
        simp() using { ((uint32)byte) <= 255u32; byte < 255; }
    }
    have result <= 255i64 by {
        arithmetic_certificate special {
            premise 0: ((uint32)byte) <= 255u32 => ((uint32)byte) <= 255u32;
            premise 1: byte < 255 => byte < 255;
            unsigned_sum_bound bounds [0, 1] => result <= 255i64;
            conclusion 0;
        }
    }
    simp();
}
```

```expect
pass
```
