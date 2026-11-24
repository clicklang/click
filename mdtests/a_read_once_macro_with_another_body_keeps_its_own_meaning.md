# A `READ_ONCE` macro with another body keeps its own meaning

A macro named `READ_ONCE` whose body is not a recognized definition is
expanded as written. This one evaluates to `0` without reading `x`, so the
claim that it returns the stored `7` fails.

```c filename=main.c
#define READ_ONCE(x) ((volatile typeof(x))0)

int32 load(int32 *p) {
    return READ_ONCE(*p);
}
```

```click
verifying "main.c";

int32 load(int32 *p) {
    owns *p;
    requires *p == 7;
    ensures result == 7;
}
```

```expect
fail: unclosed goal
```
