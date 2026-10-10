# A call owes the order of a range it hands over

`touch` holds `bytes[i..length]` with an `int` start, which a 64-bit range
reads as its sign extension. The caller passes an `int` it knows nothing
about: a negative one would lie past the end, so the range may not be in
order, and the call owes that it is. `a_call_hands_over_a_range_in_order.md`
passes a range known to be out of order.

```c filename=a_call_owes_the_order_of_a_range_it_hands_over.c
void touch(const unsigned char *bytes, int i, unsigned long length) { }
void any(const unsigned char *bytes, int i, unsigned long length) { touch(bytes, i, length); }
```

```click
verifying "a_call_owes_the_order_of_a_range_it_hands_over.c";
void touch(const uint8* bytes, int32 i, uint64 length) {
    views bytes[i..length];
} by { execute(); simp(); }
void any(const uint8* bytes, int32 i, uint64 length) {
    views bytes[0..length];
} by { execute(); simp(); }
```

```expect
fail: missing prerequisite (touch range bounds)
```
