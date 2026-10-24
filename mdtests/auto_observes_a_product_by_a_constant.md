# `auto` observes a machine product by a constant

A machine `*` whose exact result lies in its type's range is that exact
result: `to_integer(x * 3) == to_integer(x) * 3` once
`-2147483648 <= to_integer(x) * 3 <= 2147483647`. `auto` plans that
identity, as it plans one for `+` and `-`, when one factor is a constant,
so the product's exact value is affine and its two bounds follow from the
operand's. It does so at every width with a product: `int`, `unsigned`,
`long` and `unsigned long`.

```c filename=auto_observes_a_product_by_a_constant.c
int triple(int x) { return x * 3; }
unsigned twice(unsigned x) { return x * 2u; }
long scale(long x) { return x * 1000; }
unsigned long words(unsigned long n) { return n * 8ul; }
```

```click
verifying "auto_observes_a_product_by_a_constant.c";

int32 triple(int32 x) {
    requires -1000 <= x;
    requires x <= 1000;
    ensures to_integer(result) == 3 * to_integer(x);
} by {
    auto();
}

uint32 twice(uint32 x) {
    requires x <= 2147483647u32;
    ensures to_integer(result) == to_integer(x) * 2;
} by {
    auto();
}

int64 scale(int64 x) {
    requires -1000000i64 <= x;
    requires x <= 1000000i64;
    ensures to_integer(result) == to_integer(x) * 1000;
} by {
    auto();
}

uint64 words(uint64 n) {
    requires n <= 1000000u64;
    ensures to_integer(result) == 8 * to_integer(n);
} by {
    auto();
}

theorem doubled(x: uint32) {
    requires x <= 1000u32;
    ensures to_integer(x * 2u32) == to_integer(x) * 2 by { auto(); };
}
```

```expect
pass
```
