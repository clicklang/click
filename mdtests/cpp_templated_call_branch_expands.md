# A branch expansion names a templated method call

The expanded branch names the result by its position among the calls. A
preceding void call makes that position differ from the method's own count.

```cpp filename=templated_call_branch.cpp function=probe profile=normal_only
template<class T> struct Box {
    T value;
    T get() const noexcept { return value; }
};

void prepare() noexcept { return; }

int probe(const Box<int>& box) noexcept {
    prepare();
    if (box.get() == 0)
        return 2;
    return 1;
}
```

```click
verifying "templated_call_branch.cpp";

void prepare() { ensures true; }

int Box<int>::get() const {
    views this->value;
    ensures result == old(this->value);
}

int probe(const Box<int>& box) {
    views box.value;
    ensures result == 1 or result == 2;
} by {
    step();
}
```

```expect
pass
```
