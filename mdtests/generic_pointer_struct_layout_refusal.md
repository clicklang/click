# Generic pointer parameters do not erase struct layouts

```c filename=objects.c
struct item { int32 a; int32 b; };
void inspect(struct item *p) {}
```

```click
verifying "objects.c";
theorem identity<T>(p: T*) {
    ensures p == p by { normalize(); }
}
void inspect(struct item *p) { ensures true; } by {
    have p == p by { apply(identity(p)) using {}; }
}
```

```expect
fail: struct values are not yet supported
```
