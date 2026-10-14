# A checked callback read cannot invent a table alias

```c filename=callback-read.c
struct callbacks { void (*call)(int *p); };
static void target(int *p) { }
static const struct callbacks table = { .call = target };
void copy(const struct callbacks *cb, struct callbacks *out) { out->call = cb->call; }
```

```click
verifying "callback-read.c";
void copy(const struct callbacks* cb, struct callbacks* out) {
    views cb->call;
    owns out->call;
    ensures out->call == (&table)->call;
} by { execute(); simp(); }
```

```expect
fail: unclosed goal
```
