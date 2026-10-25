# `produces` refuses memory the function did not write

`init` takes `uninitialized(p[0..1])` and claims to produce `p[0..1]`, which
hands its caller initialized bytes. Its body writes nothing, so its proof is
refused at the return: memory a function returns unwritten is produced as
`uninitialized(...)`. The positive case is
[`an_initializer_produces_the_memory_it_initialized.md`](an_initializer_produces_the_memory_it_initialized.md).

```c filename=unwritten_initializer.c
void init(int *p) { }
```

```click
verifying "unwritten_initializer.c";

void init(int32* p) {
    consumes uninitialized(p[0..1]);
    produces p[0..1];
} by { execute(); solve(); }
```

```expect
fail: as initialized memory, but has not initialized every byte of it
```
