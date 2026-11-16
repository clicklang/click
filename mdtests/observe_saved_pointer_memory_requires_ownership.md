# A saved pointer does not grant memory ownership

Owning the pointer field does not own its pointee range. Naming an earlier
pointer value cannot manufacture the missing permission.

```c filename=observe_saved.c
struct box { int* data; };
void update(struct box* box) { int scratch; scratch = 1; }
```

```click
verifying "observe_saved.c";
void update(struct box* box) {
    owns *box;
} by {
    step_until(function.exit);
    observe(at(function.entry, box->data)[0..2]);
}
```

```expect
fail: observe requires the exact memory range to be held as a unit owner or view
```
