# A class template's override that breaks the generic interface is refused

`Wrap<T>::put` stores into `last` and keeps `value`, which `held` reads, so it does not establish `Holder<T>`'s
interface, `held(this) == x`, read through `Wrap<T>`'s definition. The
override is checked once, with `T` abstract, and refused there.

```cpp filename=holders.cpp function=store profile=normal_only templates=Holder<T>;Wrap<T>
template<class T> struct Holder {
    virtual void put(T x) noexcept = 0;
};

template<class T> struct Wrap : Holder<T> {
    T value;
    T last;
    void put(T x) noexcept override { last = x; }
};

void store(Holder<int>& holder, int x) noexcept {
    holder.put(x);
}
```

```click
verifying "holders.cpp";

template<class T> class Holder<T> {
    function held(this) -> T;
}
template<class T> extern void Holder<T>::put(T x) {
    ensures held(this) == x;
}
template<class T> class Wrap<T> : Holder<T> {
    function held(this) -> T { this->value }
}
template<class T> void Wrap<T>::put(T x) {
} by { execute(); simp(); }

void store(Holder<int>& holder, int x) {
    ensures held(holder) == x;
} by { execute(); simp(); }
```

```expect
fail: failed for `Wrap<T>::put.interface_ensures_0`
```
