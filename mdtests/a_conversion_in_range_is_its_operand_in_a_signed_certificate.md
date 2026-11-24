# A conversion in range is its operand in a signed certificate

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `close() using { ... }`.

```c filename=a_conversion_in_range_is_its_operand_in_a_signed_certificate.c
int next_byte(int x) { unsigned char y = x + 1; return y; }
```

```click
verifying "a_conversion_in_range_is_its_operand_in_a_signed_certificate.c";
int32 next_byte(int32 x) {
    requires 0 <= x;
    requires x < 255;
    ensures (result as int32) == ((x + 1) as int32);
} by {
    step();
    step();
    step();
    have (result as int32) == ((x + 1) as int32) by {
        close() using { at(function.entry, x < 255); at(function.entry, 0 <= x); };
    }
    known();
}
```

```expect
pass
```
