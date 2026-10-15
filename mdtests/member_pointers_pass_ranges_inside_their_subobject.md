# Member pointers pass ranges inside their subobject

A member pointer satisfies a callee's clause that stays inside the member:
one scalar member as a one-element range, and a member array as its whole
length.

```c filename=members.c
struct Pair { int32 first; int32 second; };
struct Rec { int32 arr[4]; int32 tail; };
int32 one(int32* p) { return p[0]; }
int32 four(int32* p) { return p[3]; }
int32 use_one(struct Pair* p) { return one(&p->second); }
int32 use_four(struct Rec* r) { return four(r->arr); }
```

```click
verifying "members.c";
int32 one(int32* p) {
    views p[0..1];
    ensures result == p[0];
} by { execute(); simp(); }
int32 four(int32* p) {
    views p[0..4];
    ensures result == p[3];
} by { execute(); simp(); }
int32 use_one(struct Pair* p) {
    views p->second;
    ensures result == p->second;
} by { execute(); simp(); }
int32 use_four(struct Rec* r) {
    views r->arr[0..4];
    ensures result == r->arr[3];
} by { execute(); simp(); }
```

```expect
pass
```
