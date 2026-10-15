# A one-past scalar-member pointer cannot read its sibling

`&p->first + 1` is one past `first`, an array of one element (C11
6.5.6p7-p8). It is a valid pointer to form, but not to read through, even
though `second` lives at that address and the contract grants reading it.
Address equality does not make the pointer designate `second`.

```c filename=probe.c
struct Pair { int32 first; int32 second; };
int32 probe(struct Pair* p) { return *(&p->first + 1); }
```

```click
verifying "probe.c";
int32 probe(struct Pair* p) {
    views p->first;
    views p->second;
    ensures result == p->second;
} by { execute(); simp(); }
```

```expect
fail: access outside the subobject the pointer designates
```
