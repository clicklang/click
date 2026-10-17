# A loaded pointer cannot borrow formation bounds from an address alias

The holder may contain a pointer to one scalar member while `q` designates
an enclosing byte-cast range. Equal addresses do not equate those bounds.

```c filename=loaded.c
struct Holder { int32* link; };
int32* probe(struct Holder* h, int32* q) {
    return h->link + 2;
}
```

```click
verifying "loaded.c";
int32* probe(struct Holder* h, int32* q) {
    views h->link;
    views q[0..3];
    requires address(h->link) == address(q);
    ensures true;
} by { execute(); simp(); }
```

```expect
fail: pointer arithmetic left the pointed-to object
```
