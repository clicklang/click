# The size of a record at abstract type arguments is not one number

A class template verified once for every type holds each value of its
abstract type argument in `sizeof(T)` bytes, so the size of a record holding
one, `sizeof(Pair<T>)`, is the instance's own size: `Pair<int>` takes 8 bytes
and `Pair<long long>` 16. It is no one number, so a generic method's contract
cannot prove it is 16, while the method's own postcondition about its fields
holds for every type.

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
}

void swap_ints(Pair<int>& pair) {
    owns pair;
    ensures pair.first == old(pair.second);
}
```

```expect
fail: did not retain a complete proof for `Pair<T>::swap.ensures_1`
```
