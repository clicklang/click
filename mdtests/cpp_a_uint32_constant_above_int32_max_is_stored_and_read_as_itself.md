# A C++ uint32 constant above INT32_MAX is stored and read as itself

A C++ `unsigned int` literal lowers to a `uint32` constant
(`ScalarLiteral::kernel_expression`, `MachineIntegerType::constant_term`),
so `4000000000u` is stated, stored through a reference, read back and
returned as that number.

```cpp filename=constants.cpp function=literal;stored;stated profile=normal_only
unsigned int literal() noexcept { return 4000000000u; }
unsigned int stored(unsigned int& u) noexcept {
    u = 4000000000u;
    return u;
}
unsigned int stated(const unsigned int& u) noexcept { return u; }
```

```click
verifying "constants.cpp";
unsigned int literal() {
    ensures result == 4000000000u32;
}
unsigned int stored(uint32& u) {
    owns u;
    ensures result == 4000000000u32;
    ensures u == 4000000000u32;
}
unsigned int stated(const uint32& u) {
    views u;
    requires u == 4000000000u32;
    ensures result == 4000000000u32;
}
```

```expect
pass
```
