# A C++ dereference of an observer call loads its pointee's type

`*pick(p)` dereferences the result of a call nested in an expression, which
C++ lowering normalizes into a call followed by a load
(`normalize_expression`). The load has the pointee's type, as an ordinary
`*p` has: through `unsigned char*` it reads the one byte, so the read is
neither an `int` access to a `char` object nor a read past the byte the
contract lends.

```cpp filename=observed.cpp function=pick;read_through profile=normal_only
unsigned char* pick(unsigned char* p) noexcept { return p; }
unsigned char read_through(unsigned char* p) noexcept { return *pick(p); }
```

```click
verifying "observed.cpp";
uint8* pick(uint8* p) {
    ensures result == p;
}
uint8 read_through(uint8* p) {
    views p[0..1];
    ensures result == p[0];
}
```

```expect
pass
```
