# A stored unsigned sub-word retains its promoted observation

An unsigned 16-bit store retains a low-bit mask in its word carrier. The
explicit cast certificate preserves that value when it is promoted to int32.

```c filename=lane.c
void store_lane(uint16 *out, uint32 value) {
    *out = (uint16)(int32)(value & 65535U);
}
```

```click
verifying "lane.c";
void store_lane(uint16 *out, uint32 value) {
    requires 0 <= (int32)(value & 65535u32);
    requires (int32)(value & 65535u32) <= 65535;
    requires 0 <= to_integer(value);
    requires to_integer(value) <= 65535;
    owns *out;
    ensures to_integer((int32)*out) == to_integer(*out);
} by {
    execute();
    have to_integer(*out) == to_integer(old(value)) by { arithmetic_certificate special {
        premise 0: 0 <= to_integer(old(value)) => 0 <= to_integer(old(value));
        premise 1: to_integer(old(value)) <= 65535 => to_integer(old(value)) <= 65535;
        integer_cast_identity bounds [0, 1] => to_integer(*out) == to_integer(old(value)); conclusion 0;
    } }
    have 0 <= to_integer(*out) by { rewrite(to_integer(*out) == to_integer(old(value))); assumption(); }
    have to_integer(*out) <= 65535 by { rewrite(to_integer(*out) == to_integer(old(value))); assumption(); }
    have to_integer((int32)*out) == to_integer(*out) by { arithmetic_certificate special {
        premise 0: 0 <= to_integer(*out) => 0 <= to_integer(*out);
        premise 1: to_integer(*out) <= 65535 => to_integer(*out) <= 65535;
        integer_cast_identity bounds [0, 1] => to_integer((int32)*out) == to_integer(*out); conclusion 0;
    } }
    simp() using { to_integer((int32)*out) == to_integer(*out); }
}
```

```expect
pass
```
