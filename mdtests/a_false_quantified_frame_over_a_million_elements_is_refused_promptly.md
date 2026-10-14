# A false quantified frame over a million elements is refused promptly

A byte store changes element 1 while leaving the returned element 2 alone.
The whole-range frame is false and must fail without materializing the range.

```c filename=probe.c
int32 untouched_element(int32* a) {
    unsigned char* b;
    b = (unsigned char*)(void*) a;
    b[5] = 7;
    return a[2];
}
```

```click
verifying "probe.c";
int32 untouched_element(int32* a) {
    owns a[0..1000000];
    ensures result == old(a[2]);
    ensures (0..1000000).all(|k| { a[k] == old(a[k]) });
} by { execute(); simp(); }
```

```expect
fail: (0..1000000).all
```
