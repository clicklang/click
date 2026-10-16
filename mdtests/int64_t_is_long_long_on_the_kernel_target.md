# `int64_t` is `long long` on the kernel target

The Linux kernel defines `s64` and `u64`, and with them `int64_t` and
`uint64_t`, as `long long` and `unsigned long long`, while `size_t` stays
`unsigned long`. In `kernel` mode, a pointer to `int64_t`
therefore converts to and from `long long *` without a cast, and
`__builtin_types_compatible_p` reports the kernel's identities.

```c filename=main.c
long long *values(int64_t *p) {
    long long *q = p;
    return q;
}

uint64_t *words(unsigned long long *p) {
    return p;
}

int identities(void) {
    return __builtin_types_compatible_p(int64_t, long long)
        && __builtin_types_compatible_p(uint64_t, unsigned long long)
        && !__builtin_types_compatible_p(int64_t, long)
        && __builtin_types_compatible_p(size_t, unsigned long);
}
```

```click
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "main.c";

long long *values(int64_t *p) {
    ensures result == p by auto;
}

uint64_t *words(unsigned long long *p) {
    ensures result == p by auto;
}

int32 identities() {
    ensures result == 1 by { execute(); normalize(); }
}
```

```expect
pass
```
