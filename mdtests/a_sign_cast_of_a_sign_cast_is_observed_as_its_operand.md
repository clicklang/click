# a sign cast of a sign cast is observed as its operand

A conversion between `int32` and `uint32` is σ, a node of its own, and σ of
σ is kept as written: `(int32)((uint32)a)` is two σ nodes over `a`, not
`a`. Rule W reads an observation through σ, which keeps its operand's 32
bits, so `to_integer` of the round trip at `int32` reads as `to_integer(a)`.
The reading goes through every σ of the chain. When it read only the outer
one, the inner `uint32` σ(a) observed at `int32` had no reading, so the
observation did not exist: the round trips below lowered to "invalid machine
integer representation", the written `to_integer((a as uint32) as int32)`
to "no single evaluation path", and `+ 0` over it panicked building the
addition's domain. In
`mdtests/a_bounded_wrapped_difference_does_not_define_the_signed_one.md` the
implicit closer spelled such an observation and stopped at the same
lowering error instead of reporting the signed overflow.

```c filename=a_sign_cast_of_a_sign_cast_is_observed_as_its_operand.c
int32 round_trip(int32 a) {
    return (int32)((uint32)a);
}

uint32 unsigned_round_trip(uint32 u) {
    return (uint32)((int32)u);
}

int32 written(int32 a) {
    return a;
}
```

```click
verifying "a_sign_cast_of_a_sign_cast_is_observed_as_its_operand.c";

int32 round_trip(int32 a) {
    ensures to_integer(result) == to_integer(a);
}

uint32 unsigned_round_trip(uint32 u) {
    ensures to_integer(result) == to_integer(u);
}

int32 written(int32 a) {
    ensures to_integer((a as uint32) as int32) == to_integer(a);
    ensures to_integer(((a as uint32) as int32) + 0) == to_integer(a);
}
```

```expect
pass
```
