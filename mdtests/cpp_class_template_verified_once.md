# A C++ class template's methods are verified once for every type

A class template the project names with its parameters, `Cell<T>`, is
exported at an abstract type argument as well as at each instance a caller
uses. Its methods' bodies are checked there once, with `T` a value that is
only copied: `template<class T> void Cell<T>::set(T v)` states and proves the
method for every `T`. Each instance's method, `Cell<int>::set` and
`Cell<unsigned int>::read`, has that contract at its own types and record
layout, and its body is not checked again. `round_trip` calls the methods at
two instances.

```cpp filename=cell.cpp function=round_trip profile=normal_only templates=Cell<T>
template<class T> class Cell {
    T value;
    unsigned long count = 0;

public:
    void set(T v) noexcept {
        value = v;
        count = count + 1;
    }

    T get() const noexcept { return value; }

    void read(T& out) const noexcept { out = value; }
};

int round_trip(Cell<int>& small, Cell<unsigned int>& large, int x, unsigned int y) noexcept {
    small.set(x);
    large.set(y);
    unsigned int out = 0;
    large.read(out);
    if (out != y) {
        return 0;
    }
    return small.get();
}
```

```click
verifying "cell.cpp";

template<class T> void Cell<T>::set(T v) {
    owns *this;
    requires this->count < 1000u64;
    ensures this->value == v;
    ensures this->count == old(this->count) + 1u64;
} by {
    execute();
    simp();
}

template<class T> T Cell<T>::get() const {
    views *this;
    ensures result == this->value;
} by {
    execute();
    simp();
}

template<class T> void Cell<T>::read(T& out) const {
    views *this;
    owns out;
    ensures out == this->value;
} by {
    execute();
    simp();
}

int round_trip(Cell<int>& small, Cell<unsigned int>& large, int x, unsigned int y) {
    owns small;
    owns large;
    requires small.count < 1000u64;
    requires large.count < 1000u64;
    ensures result == x;
} by {
    execute();
    simp();
}
```

```expect
pass
```
