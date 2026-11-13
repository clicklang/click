# A C++ sidecar spells `std::byte` as Click's `uint8`

`std::byte` is a byte. A C++ sidecar may write it where it writes a type, as
in `sizeof(std::byte)`, and reads it as `uint8`; `const std::byte` is
`const uint8`.

```cpp filename=byte.cpp function=byte_size profile=normal_only
unsigned long byte_size() noexcept { return 1; }
```

```click
verifying "byte.cpp";

unsigned long byte_size() {
    ensures result == sizeof(std::byte);
    ensures result == sizeof(const std::byte);
    ensures result == sizeof(uint8);
}
```

```expect
pass
```
