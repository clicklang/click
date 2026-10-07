# Range-checked legacy cast observations

Ordinary casts and the shared modulo conversion boundary retain their existing
32/64-bit terms. Exact observation requires two explicit destination-range
bounds. These casts include Bitcoin's fast-path fee, amount and denominator
conversions.

```click
theorem cast0(value: int64) {
    requires 0 <= to_integer(value);
    requires to_integer(value) <= 8589934591;
    ensures to_integer((uint64)value) == to_integer(value) by {
        arithmetic_certificate special {
            premise 0: 0 <= to_integer(value) => 0 <= to_integer(value);
            premise 1: to_integer(value) <= 8589934591 => to_integer(value) <= 8589934591;
            integer_cast_identity bounds [0, 1] => to_integer((uint64)value) == to_integer(value); conclusion 0;
        }
    }
}
theorem cast1(value: int32) {
    requires 0 <= to_integer(value);
    requires to_integer(value) <= 2147483647;
    ensures to_integer((uint64)value) == to_integer(value) by {
        arithmetic_certificate special {
            premise 0: 0 <= to_integer(value) => 0 <= to_integer(value);
            premise 1: to_integer(value) <= 2147483647 => to_integer(value) <= 2147483647;
            integer_cast_identity bounds [0, 1] => to_integer((uint64)value) == to_integer(value); conclusion 0;
        }
    }
}
theorem cast2(value: int32) {
    requires 1 <= to_integer(value);
    requires to_integer(value) <= 2147483647;
    ensures to_integer((uint32)value) == to_integer(value) by {
        arithmetic_certificate special {
            premise 0: 1 <= to_integer(value) => 1 <= to_integer(value);
            premise 1: to_integer(value) <= 2147483647 => to_integer(value) <= 2147483647;
            integer_cast_identity bounds [0, 1] => to_integer((uint32)value) == to_integer(value); conclusion 0;
        }
    }
}
theorem cast3(value: uint32) {
    requires 0 <= to_integer(value);
    requires to_integer(value) <= 4294967295;
    ensures to_integer((uint64)value) == to_integer(value) by {
        arithmetic_certificate special {
            premise 0: 0 <= to_integer(value) => 0 <= to_integer(value);
            premise 1: to_integer(value) <= 4294967295 => to_integer(value) <= 4294967295;
            integer_cast_identity bounds [0, 1] => to_integer((uint64)value) == to_integer(value); conclusion 0;
        }
    }
}
```

```expect
pass
```
