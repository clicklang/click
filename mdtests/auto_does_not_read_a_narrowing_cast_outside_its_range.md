# `auto` does not read a narrowing cast outside its range

The negative of
[`auto_reads_a_narrowing_cast_inside_its_range.md`](auto_reads_a_narrowing_cast_inside_its_range.md).
`x` may be `4294967296`, whose `(uint32)` cast is `0`, so `1u32 <= y` is false
for some `x` and the cast identity's upper bound cannot be proved.

```c filename=narrow_wide.c
unsigned narrow_wide(unsigned long x) { unsigned y = x; return y; }
```

```click
verifying "narrow_wide.c";

uint32 narrow_wide(uint64 x) {
    requires 1u64 <= x;
    requires x < 5000000000u64;
    ensures 1u32 <= result;
} by {
    step();
    step();
    have 1u32 <= y by { auto(); }
}
```

```expect
fail: could not establish `1u32 <= y`
```
