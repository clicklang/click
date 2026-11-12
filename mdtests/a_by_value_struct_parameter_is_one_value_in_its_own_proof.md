# A by-value struct parameter is one value in its function's own proof

`first_plus_one` takes `struct pair` by value and returns `p.a + 1`. In the
function's own proof the parameter is its input: `p.a` in the contract names
the field's value at entry, the body's private copy is made from that value,
and the result is computed from it. So the arithmetic postcondition is a fact
about one spelled value and the implicit closer proves it from the
requirement.

The entry does not put another object behind the parameter. Were the input
copied from an argument with no name, the result would be `that + 1` while the
contract read `p.a`, and the bound `p.a <= 1000u32` could not be cited for it.

```c filename=by_value_arithmetic.c
struct pair { uint32 a; uint32 b; };

uint32 first_plus_one(struct pair p) {
    return p.a + 1;
}
```

```click
verifying "by_value_arithmetic.c";

uint32 first_plus_one(struct pair p) {
    requires p.a <= 1000u32;
    ensures result == p.a + 1u32;
}
```

```expect
pass
```
