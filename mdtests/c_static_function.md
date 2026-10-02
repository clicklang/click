# A file-scope `static` function is a translation-unit-local function

`static` without `inline` gives a function internal linkage. It differs from
`static inline` only in an optimization hint, so Click treats it the same
way: the function is local to its translation unit and a call executes its
checked body. A forward `static` prototype and file-scope `static` objects
may surround it.

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
    requires value < 100;
    ensures result == value + 2 by auto;
}
```

```expect
pass
```
