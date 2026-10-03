# A file-scope `static` function is a translation-unit-local function

`static` without `inline` gives a function internal linkage. It differs from
`static inline` only in an optimization hint, so Click treats it the same
way: the function is local to its translation unit. A call applies its
verified contract, as for any function, so `run` must meet `add_one`'s
precondition at both calls: `value < 99` makes the inner result less than 100.
The proof steps the inner call on its own, naming its result `r`, and states
that bound before the outer call.
A forward `static` prototype and file-scope `static` objects may surround it.

```c filename=c_static_function.c
static int add_one(int value);
static int calls = 0;

static const int *same(const int *pointer) {
    return pointer;
}

static int add_one(int value) {
    return value + 1;
}

int32 run(int32 value) {
    return add_one(add_one(value));
}
```

```click
verifying "c_static_function.c";

int32 add_one(int32 value) {
    requires value < 100;
    ensures result == value + 1 by auto;
}

int32 run(int32 value) {
    requires value < 99;
    ensures result == value + 2;
} by {
    let r = step(add_one(value), {});
    apply(int32_increment_upper_bound(value, 99)) using { value < 99; }
    have r < 100 by { arithmetic() using { r == value + 1; value + 1 <= 99; } }
    step();
    step();
    simp();
}
```

```expect
pass
```
