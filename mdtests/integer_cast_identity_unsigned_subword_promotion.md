# A stored unsigned sub-word retains its promoted observation

The proof names the stored expression at both widths. The entry bounds
relate the narrowed value to the original parameter.

```c filename=lane.c
void store_lane(uint16 *out, uint32 value) {
    *out = (uint16)(int32)(value & 65535U);
}
```

```click
verifying "lane.c";
void store_lane(uint16 *out, uint32 value) {
    requires 0 <= (value & 65535u32) as int32;
    requires (value & 65535u32) as int32 <= 65535;
    requires 0 <= to_integer(value);
    requires to_integer(value) <= 65535;
    owns *out;
    ensures to_integer(*out as int32) == to_integer(*out);
} by {
    step_until(function.exit);
    have to_integer(*out) == to_integer((((old(value) & 65535u32) as int32) as uint16)) by known();
    have to_integer((((old(value) & 65535u32) as int32) as uint16)) == to_integer(old(value)) by known();
    have to_integer(*out) == to_integer(old(value)) by known();
    have to_integer(*out as int32) == to_integer((((old(value) & 65535u32) as int32) as uint16) as int32) by known();
    have to_integer((((old(value) & 65535u32) as int32) as uint16) as int32) == to_integer((((old(value) & 65535u32) as int32) as uint16)) by known();
    known();
}
```

```expect
pass
```
