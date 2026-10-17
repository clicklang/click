# An allocation supplies formation bounds without read authority

Holding allocation identity permits forming a member address and a one-past
pointer. It does not give ownership or a view of the object's bytes.

```c filename=allocation.c
struct Pair { int32 first; int32 second; };
int32* field(struct Pair* p) { return &p->second; }
int32* one_past(int32* p) { return p + 2; }
```

```click
verifying "allocation.c";
int32* field(struct Pair* p) {
    owns allocation(p, sizeof(struct Pair));
    ensures result == &p->second;
} by { execute(); simp(); }
int32* one_past(int32* p) {
    owns allocation(p, 8);
    ensures result == p + 2;
} by { execute(); simp(); }
```

```expect
pass
```
