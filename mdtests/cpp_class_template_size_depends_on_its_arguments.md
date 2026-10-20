# The size of a record at abstract type arguments is not one number

A class template verified once for every type is laid out at its abstract
type argument with a machine word for each value of it, and each instance as
Clang lays it out: `Pair<T>` takes 16 bytes there and `Pair<int>` 8. A
generic method's contract that read `sizeof(Pair<T>)` could prove a size no
instance has, so the size of a record holding a value of an abstract type is
refused.

```cpp filename=pair.cpp function=swap_ints profile=normal_only templates=Pair<T>
template<class T> class Pair {
    T first;
    T second;

public:
    void swap() noexcept {
        T held = first;
        first = second;
        second = held;
    }
};

void swap_ints(Pair<int>& pair) noexcept { pair.swap(); }
```

```click
verifying "pair.cpp";

template<class T> void Pair<T>::swap() {
    owns *this;
    ensures this->first == old(this->second);
    ensures sizeof(Pair<T>) == 16;
} by {
    execute();
    simp();
}

void swap_ints(Pair<int>& pair) {
    owns pair;
    ensures pair.first == old(pair.second);
} by {
    execute();
    simp();
}
```

```expect
fail: the size of `Pair<T>` depends on its abstract type arguments
```
