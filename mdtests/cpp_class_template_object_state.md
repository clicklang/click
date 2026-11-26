# A C++ class template's object state is verified once for every type

A generic `class` block declares the object state of a polymorphic class
template, `template<class T> class Holder<T> { function held(this) -> T; }`:
its object is the generic resource `Holder<T>::object`, and each instance a
caller uses, `Holder<int>` and `Holder<unsigned int>`, has it at its type.
A named contract can refer to the instance directly.
`Wrap<T>` defines `held` on its own memory for every `T`, so its overrides
are verified once, against `Holder<T>`'s interface read through the
definition. A caller passing a `Wrap<int>` as a `Holder<int>&` knows after
the call that its `value` is the object's new `held`, and one passing a
`const Wrap<unsigned int>&` keeps its `value`.

```cpp filename=holders.cpp function=store;through;peek;through_peek profile=normal_only templates=Holder<T>;Wrap<T>
template<class T> struct Holder {
    virtual void put(T x) noexcept = 0;
    virtual T get() const noexcept = 0;
};

template<class T> struct Wrap : Holder<T> {
    T value;
    void put(T x) noexcept override { value = x; }
    T get() const noexcept override { return value; }
};

int store(Holder<int>& holder, int x) noexcept {
    holder.put(x);
    int got = holder.get();
    return got;
}

int through(Wrap<int>& wrap, int x) noexcept {
    int got = store(wrap, x);
    return got;
}

unsigned int peek(const Holder<unsigned int>& holder) noexcept {
    unsigned int got = holder.get();
    return got;
}

unsigned int through_peek(const Wrap<unsigned int>& wrap) noexcept {
    unsigned int got = peek(wrap);
    return got;
}
```

```click
verifying "holders.cpp";

import "interfaces/cpp_class_template_object_state.interface.click";
template<class T> class Wrap<T> : Holder<T> {
    function held(this) -> T { this->value }
}
contract void HoldUnsigned(int* p) {
    owns held_object: Holder<unsigned int>::object(p);
}
template<class T> void Wrap<T>::put(T x) {
}
template<class T> T Wrap<T>::get() const {
}

int store(Holder<int>& holder, int x) {
    ensures result == x;
    ensures held(holder) == x;
}

int through(Wrap<int>& wrap, int x) {
    owns wrap;
    ensures result == x;
    ensures wrap.value == x;
}

unsigned int peek(const Holder<unsigned int>& holder) {
    ensures result == held(holder);
}

unsigned int through_peek(const Wrap<unsigned int>& wrap) {
    views wrap;
    ensures result == wrap.value;
}
```

```expect
pass
```
