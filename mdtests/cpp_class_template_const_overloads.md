# A class template's const and mutable overloads are told apart by constness

`Cell<T>` has a mutable and a `const` overload of `get`, which share the
path `Cell<T>::get`: the mutable one counts its reads. The sidecar states
each once as a template method, and each head names the overload whose
receiver constness and parameter types it writes: `T Cell<T>::get()` the
mutable one and `T Cell<T>::get() const` the `const` one. Each instance a
call names, `Cell<int>::get` through a mutable and through a `const`
reference, is written out from the overload with its constness, so only the
mutable call changes `reads`.

```cpp filename=cell.cpp function=pick profile=normal_only templates=Cell<T>
template<class T> class Cell {
    T value;
    unsigned long reads = 0;

public:
    T get() noexcept {
        reads = reads + 1;
        return value;
    }

    T get() const noexcept { return value; }
};

int pick(Cell<int>& counted, const Cell<int>& plain, int which) noexcept {
    if (which == 0) {
        return counted.get();
    }
    return plain.get();
}
```

```click
verifying "cell.cpp";

template<class T> T Cell<T>::get() {
    owns *this;
    requires this->reads < 1000u64;
    ensures result == this->value;
    ensures this->reads == old(this->reads) + 1u64;
}

template<class T> T Cell<T>::get() const {
    views *this;
    ensures result == this->value;
}

int pick(Cell<int>& counted, const Cell<int>& plain, int which) {
    owns counted;
    views plain;
    requires counted.reads < 1000u64;
    ensures which == 0 implies result == counted.value;
    ensures which != 0 implies result == plain.value;
    ensures which != 0 implies counted.reads == old(counted.reads);
}
```

```expect
pass
```
