# A C++ `unsigned int` cell read as `int` is its sign cast

The C++ importer reinterprets an object pointer only as a byte pointer, so a
C++ program reads an `unsigned int` cell at `int` through a conversion of
the `unsigned int` read: the load takes its 32-bit kind from the reference's
type, and `static_cast<int>` is the sign cast σ. `4294967295u` read so is
`-1`, stored or stated; the plain `unsigned int` read is the control.

```cpp filename=signedness.cpp function=read_signed;read_unsigned;store_and_read_signed profile=normal_only
int read_signed(const unsigned int& u) noexcept { return static_cast<int>(u); }
unsigned int read_unsigned(const unsigned int& u) noexcept { return u; }
int store_and_read_signed(unsigned int& u) noexcept {
    u = 4294967295u;
    return static_cast<int>(u);
}
```

```click
verifying "signedness.cpp";
int read_signed(const uint32& u) {
    views u;
    requires u == 4294967295u32;
    ensures result == -1;
} by { execute(); simp(); }
unsigned int read_unsigned(const uint32& u) {
    views u;
    requires u == 4294967295u32;
    ensures result == 4294967295u32;
} by { execute(); simp(); }
int store_and_read_signed(uint32& u) {
    owns u;
    ensures result == -1;
    ensures u == 4294967295u32;
} by { execute(); simp(); }
```

```expect
pass
```
