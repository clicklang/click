# A checked function-pointer read retains its table alias

```c filename=callback-read.c
struct callbacks { void (*call)(int *p); };
static void target(int *p) { }
static const struct callbacks table = { .call = target };
void copy(const struct callbacks *cb, struct callbacks *out) { out->call = cb->call; }
```

```click
verifying "callback-read.c";
void copy(const struct callbacks* cb, struct callbacks* out) {
    requires cb == &table;
    views cb->call;
    owns out->call;
    ensures out->call == (&table)->call;
} by {
    have separate(memory(out->call), memory(cb->call)) by assumption();
    mark write;
    have cb->call == (&table)->call by { assumption(); }
    step();
    have at(write, cb->call) == table.call by {
        normalize() using {
            at(write, cb->call) == at(write, table.call);
            cb == &table;
        };
    }
    step();
    solve();
}
```

```expect
pass
```
