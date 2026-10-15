# Scalar-member pointer domains: helper

A modular reader cannot acquire a view through a one-past scalar pointer.

```c filename=probe.c
struct Pair { int32 first; int32 second; };
int32 read(int32* p) { return *p; }
int32 probe(struct Pair* p) { return read(&p->first + 1); }
```

```click
verifying "probe.c";
int32 probe(struct Pair* p) {
    views p->first;
    views p->second;
    ensures result == p->second;
} by { execute(); simp(); }
int32 read(int32* p) { views *p; ensures result == *p; } by { execute(); simp(); }
```

```expect
fail: selected object domain
```
