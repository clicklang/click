# A cast does not supply read permission

```c filename=read.c
struct base { int32 tag; };
struct item { struct base base; int32 value; };
int32 read(struct base* p) { return ((struct item*)(void*)p)->value; }
```

```click
verifying "read.c";
int32 read(struct base* p) {
    views p->tag;
    ensures result == (p as (void *) as (struct item *))->value;
} by { step_until(function.exit); normalize(); }
```

```expect
fail: missing resource fact
```
