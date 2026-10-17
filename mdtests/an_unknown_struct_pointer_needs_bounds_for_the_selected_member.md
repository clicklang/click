# An unknown struct pointer needs bounds for the selected member

A pointer's type does not prove that it designates a whole struct. The first
member's view cannot justify selecting the second member.

```c filename=member.c
struct Pair { int32 first; int32 second; };
int32* probe(struct Pair* p) {
    return &p->second;
}
```

```click
verifying "member.c";
int32* probe(struct Pair* p) {
    views p->first;
    ensures true;
} by { execute(); simp(); }
```

```expect
fail: access outside the subobject the pointer designates
```
