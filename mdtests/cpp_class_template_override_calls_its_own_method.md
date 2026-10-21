# A class template's override calls its own method with a value of its type

`Wrap<T>::put` passes its argument, a value of the abstract type `T`, to
`Wrap<T>::assign`, a method of the same template at the same argument, which
the generic body may call as it calls any of its own methods: the value is
passed as it was read. `Wrap<T>` also writes a destructor, which no local
runs here, since the class is only reached by reference; it is the record's
own, exported and verified once for every `T` with the methods. `store`'s
proof names the holder's object state, `held(holder)`, as its clauses do.

```cpp filename=holders.cpp function=store;through profile=normal_only templates=Holder<T>;Wrap<T>
template<class T> struct Holder {
    virtual void put(T x) noexcept = 0;
    virtual T get() const noexcept = 0;
};

template<class T> struct Wrap : Holder<T> {
    T value;
    int puts;
    ~Wrap() noexcept { puts = 0; }
    void assign(T x) noexcept { value = x; }
    void put(T x) noexcept override { assign(x); }
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
```

```click
verifying "holders.cpp";

template<class T> class Holder<T> {
    function held(this) -> T;
}
template<class T> extern void Holder<T>::put(T x) {
    ensures held(this) == x;
}
template<class T> extern T Holder<T>::get() const {
    ensures result == held(this);
}
template<class T> class Wrap<T> : Holder<T> {
    function held(this) -> T { this->value }
}
template<class T> void Wrap<T>::assign(T x) {
    ensures this->value == x;
} by { execute(); simp(); }
template<class T> void Wrap<T>::put(T x) {
} by { execute(); simp(); }
template<class T> T Wrap<T>::get() const {
} by { execute(); simp(); }
template<class T> Wrap<T>::~Wrap() {
    owns *this;
    ensures this->puts == 0;
} by { execute(); simp(); }

theorem stored_value(v: int32, x: int32) {
    requires v == x;
    ensures x == v by { simp(); }
}

int store(Holder<int>& holder, int x) {
    ensures result == x;
    ensures held(holder) == x;
} by {
    execute();
    apply(stored_value(held(holder), x));
    simp();
}

int through(Wrap<int>& wrap, int x) {
    owns wrap;
    ensures result == x;
    ensures wrap.value == x;
} by { execute(); simp(); }
```

```expect
pass
```
