# A call hands over a range in order

A callee holding `bytes[i..n]` is given `i <= n` on entry, and `f` below
proves `ensures i <= n` from that alone. A caller holding `bytes[0..8]`
covers `bytes[5..2]` by its endpoints, since `0 <= 5` and `2 <= 8`, but
handing it over would give `f` the false `5 <= 2`. The call is refused.

`a_call_owes_the_order_of_a_range_it_hands_over.md` passes a start that is
not known to be in order.

```c filename=a_call_hands_over_a_range_in_order.c
int f(const unsigned char *bytes, int i, int n) { return 0; }
int g(const unsigned char *bytes) { return f(bytes, 5, 2); }
```

```click
verifying "a_call_hands_over_a_range_in_order.c";
int32 f(const uint8* bytes, int32 i, int32 n) {
    views bytes[i..n];
    ensures i <= n;
} by { execute(); simp(); }
int32 g(const uint8* bytes) {
    views bytes[0..8];
    ensures 5 <= 2;
} by { execute(); simp(); }
```

```expect
fail: `f` would be handed a range that ends before it starts
```
