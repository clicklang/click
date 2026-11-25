# A scalar pointer alias does not acquire a struct stride

```c filename=objects.c
struct item { uint8 tag; int64 value; };
```

```click
verifying "objects.c";
theorem inspect(p: struct item*) {
    let q: int32* = (p as (void *)) as (int32 *);
    ensures contains(memory(q[0..1]), memory(q[1])) by { close(); }
}
```

```expect
fail: could not establish `contains(memory(((p as (void *)) as (int32 *))[0..1]), memory(((p as (void *)) as (int32 *))[1]))`
```
