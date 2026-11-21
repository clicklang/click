# Reading a caller-supplied Boolean field

```c filename=flag.c
struct Flag { _Bool enabled; int32 padding; };
_Bool flag(struct Flag *p) { return p->enabled; }
```

```click
verifying "flag.c";
Bool flag(struct Flag* p) {
    views *p;
    ensures result == old(p->enabled);
}
```

```expect
pass
```
