# an entry `views` clause names the entry address

`views p->buf[0..n]` is a range spelled through a load. The entry partition
lowers it at the *entry* state, so the fact it produces names the address
`p->buf` held on entry. The body then stores a different pointer into that
field, and the postcondition reads through the new `p->buf`, which is
`other` — an address the contract says nothing about. The entry fact does
not reach it.

```c filename=an_entry_view_names_the_entry_address.c
struct holder {
    int32 *buf;
};

void f(struct holder *p, int32 *other, int32 n) {
    p->buf = other;
}
```

```click
verifying "an_entry_view_names_the_entry_address.c";

void f(struct holder* p, int32* other, int32 n) {
    requires 0 < n;
    requires p->buf[0] == 5;
    owns *p;
    views p->buf[0..n];
    ensures p->buf[0] == 5;
} by { execute(); simp(); }
```

```expect
fail: `other[0]` may have changed since earlier in this function: the store to `p->buf` may have written `other[0]`. Establish that the two accesses touch separate bytes.
```
