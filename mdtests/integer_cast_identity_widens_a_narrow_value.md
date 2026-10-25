# `integer_cast_identity` widens a narrow value

The explicit certificate behind
[`auto_widens_a_narrow_value_into_a_containing_type.md`](auto_widens_a_narrow_value_into_a_containing_type.md).
A widening of an 8- or 16-bit value is the same word, or the 64-bit
extension of it, read at a type that contains the source. A parameter is a
binder, whose word is a carrier only through the range its entry filed, so
the certificate cites those two facts as filed, `(int32)x >= lo` and
`(int32)x <= hi`; bounds on the narrow observation `to_integer(x)` alone
are not enough.

```c filename=widen_cert.c
int widen8(signed char x) { return x; }
long widen8l(signed char x) { return x; }
unsigned int widenu8(unsigned char x) { return x; }
unsigned long widenu16(unsigned short x) { return x; }
```

```click
verifying "widen_cert.c";

int widen8(signed char x) {
    ensures to_integer(result) == to_integer(x);
} by {
    step_until(function.exit);
    arithmetic_certificate rules {
        premise 0: (int32)old(x) >= -128 => (int32)old(x) >= -128;
        premise 1: (int32)old(x) <= 127 => (int32)old(x) <= 127;
        integer_cast_identity bounds [0, 1] => to_integer(result) == to_integer(old(x));
        conclusion 0;
    }
}

long widen8l(signed char x) {
    ensures to_integer(result) == to_integer(x);
} by {
    step_until(function.exit);
    arithmetic_certificate rules {
        premise 0: (int32)old(x) >= -128 => (int32)old(x) >= -128;
        premise 1: (int32)old(x) <= 127 => (int32)old(x) <= 127;
        integer_cast_identity bounds [0, 1] => to_integer(result) == to_integer(old(x));
        conclusion 0;
    }
}

unsigned int widenu8(unsigned char x) {
    ensures to_integer(result) == to_integer(x);
} by {
    step_until(function.exit);
    arithmetic_certificate rules {
        premise 0: (int32)old(x) >= 0 => (int32)old(x) >= 0;
        premise 1: (int32)old(x) <= 255 => (int32)old(x) <= 255;
        integer_cast_identity bounds [0, 1] => to_integer(result) == to_integer(old(x));
        conclusion 0;
    }
}

unsigned long widenu16(unsigned short x) {
    ensures to_integer(result) == to_integer(x);
} by {
    step_until(function.exit);
    arithmetic_certificate rules {
        premise 0: (int32)old(x) >= 0 => (int32)old(x) >= 0;
        premise 1: (int32)old(x) <= 65535 => (int32)old(x) <= 65535;
        integer_cast_identity bounds [0, 1] => to_integer(result) == to_integer(old(x));
        conclusion 0;
    }
}
```

```expect
pass
```
