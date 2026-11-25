# A cast does not supply read permission

`p` is a parameter, so its bounds are opaque, and converting it through
`void *` keeps them: the only evidence for them is `views p->tag`, which does
not cover `value`.

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
} by { step_until(function.exit); close(); }
```

```expect
fail: access outside the subobject the pointer designates
```
