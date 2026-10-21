# A field written through its own alias is not framed

`h->data` points at `h` itself, so the loop's store `h->data[i] = 1` writes
the low bytes of the field it reads its base from. The field may not be
carried across that store. Before the loaded-pointer encoding the verifier
panicked here with a conflicting logical pointer definition.

```c filename=self-alias.c
struct holder { int32 *data; };
void f(struct holder *h, int32 n) {
    int32 i = 0;
    while (i < n) { h->data[i] = 1; i++; }
}
```

```click
verifying "self-alias.c";
void f(struct holder *h, int32 n) {
    requires n == 1;
    owns *h;
    requires h->data == (int32 *)h;
    ensures h->data == old(h->data);
} by { execute(); simp(); }
```

```expect
fail: `ensures h->data == old(h->data)` failed for `f.ensures_0`
```
