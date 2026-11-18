# Typed assignment replaces initialization in the later allocation word

```c filename=fields.c
struct fields { unsigned int prefix : 31, written : 10, unwritten : 12; };

int answer(void) {
    struct fields source;
    struct fields target = { 1, 2, 3 };
    source.written = 257;
    struct fields *out = &target;
    *out = source;
    return out->unwritten;
}
```

```click
verifying "fields.c";
int32 answer() { ensures result == result; }
```

```expect
fail:read of uninitialized storage
```
