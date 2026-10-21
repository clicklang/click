# Calls while a guard lives execute through its unwind cleanup

While `g` lives, each call in `f` is wrapped in the unwind cleanup that runs
`~Guard` if the call throws. `set` throws nothing, so each wrapped call has
one successor: `execute()` steps over it as `step()` does instead of
splitting it into returned and threw arms, and the second wrapped call
directly after the first is the next statement of the proof's source.

```cpp filename=g.cpp function=f profile=normal_only
struct Guard {
    int* p;
    Guard(int& v) noexcept : p(&v) {}
    ~Guard() noexcept { *p = 0; }
};

void set(int& out) noexcept { out = 1; }

int f(int& v) noexcept {
    Guard g(v);
    int out = 0;
    set(out);
    set(out);
    return out;
}
```

```click
verifying "g.cpp";

Guard::Guard(int32& v) {
    owns this->p;
    ensures this->p == &v;
} by { execute(); simp(); }

Guard::~Guard() {
    owns this->p;
    owns this->p[0..1];
    ensures this->p == old(this->p);
    ensures this->p[0] == 0;
} by { execute(); simp(); }

void set(int32& out) {
    owns out;
    ensures out == 1;
} by { execute(); simp(); }

int f(int32& v) {
    owns v;
    ensures result == 1;
    ensures v == 0;
} by { execute(); simp(); }
```

```expect
pass
```
