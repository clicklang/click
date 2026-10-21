# A generic class template's instance method has no contract of its own

`Cell<int>::set` is an instance of `Cell<T>::set`, which the project verifies
once for every type: the instance has the generic method's contract at its
types, written out from it. A sidecar that writes the instance's contract
itself is refused, whatever the contract says.

```cpp filename=cell.cpp function=store profile=normal_only templates=Cell<T>
template<class T> class Cell {
    T value;

public:
    void set(T v) noexcept { value = v; }
};

void store(Cell<int>& cell, int x) noexcept { cell.set(x); }
```

```click
verifying "cell.cpp";

template<class T> void Cell<T>::set(T v) {
    owns *this;
    ensures this->value == v;
} by {
    execute();
    simp();
}

void Cell<int>::set(int v) {
    owns *this;
    ensures this->value == v;
} by {
    execute();
    simp();
}

void store(Cell<int>& cell, int x) {
    owns cell;
    ensures cell.value == x;
} by {
    execute();
    simp();
}
```

```expect
fail: `Cell<int>::set` is an instance of a generic class template's method
```
