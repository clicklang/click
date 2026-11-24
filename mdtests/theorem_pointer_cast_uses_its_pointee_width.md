# Theorem instantiation uses a scalar pointer cast's pointee width

The cast from a struct pointer to `int32*` gives the range a four-byte
stride. The checked theorem application must instantiate the same range as
the explicit premise.

```c filename=pointer_cast.c
struct table { int a; int b; int c; };
void check(struct table *table, int *p) {}
```

```click
verifying "pointer_cast.c";

theorem keep(words: int32*, written: Resource) {
    requires separate(written, memory(words[0..2]));
    ensures separate(written, memory(words[0..2])) by close();
}

void check(struct table* table, int* p) {
    requires separate(memory(p[0..1]), memory((table as (int32 *))[0..2]));
    ensures true;
} by {
    apply(keep(table as (int32 *), memory(p[0..1])));
}
```

```expect
pass
```
