# A stored unsigned sub-word retains its promoted observation

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `solve() using { ... }`.

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
    have to_integer(*out) == to_integer(old(value)) by { solve() using { 0 <= to_integer(old(value)); to_integer(old(value)) <= 65535; }; }
    have to_integer(*out as int32) == to_integer(*out) by { solve() using { 0 <= to_integer(*out); to_integer(*out) <= 65535; }; }
    solve() using { to_integer(*out as int32) == to_integer(*out); };
}
```

```expect
pass
```
