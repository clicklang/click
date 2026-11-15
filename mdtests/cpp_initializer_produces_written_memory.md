# A C++ initializer produces the memory it wrote

A modular initializer accepts unwritten storage and returns initialized storage.
Its caller starts with an uninitialized scalar and reads it only after the call.

```cpp filename=initializer.cpp function=caller profile=normal_only
void init(unsigned int* p, unsigned int value) noexcept { *p = value; }
unsigned int caller(unsigned int value) noexcept {
    unsigned int x;
    init(&x, value);
    return x;
}
```

```click
verifying "initializer.cpp";

void init(uint32* p, uint32 value) {
    consumes uninitialized(p[0..1]);
    produces p[0..1];
    ensures p[0] == value;
}

uint32 caller(uint32 value) {
    ensures result == value;
}
```

```expect
pass
```
