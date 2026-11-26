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
    have separate(memory(out->call), memory(cb->call)) by close();
    mark write;
    have cb->call == (&table)->call by { close(); }
    step();
    have separate(statement(0).footprint, memory(table.call)) by {
        rewrite(&table, cb);
        close() using { separate(memory(out->call), memory(cb->call)); };
    }
    have table.call == at(write, table.call) by {
        preserve(memory(table.call), statement(0));
    }
    have at(write, cb->call) == table.call by {
        rewrite(table.call, at(write, table.call));
        close();
    }
    step();
    close();
}
```

```expect
pass
```
