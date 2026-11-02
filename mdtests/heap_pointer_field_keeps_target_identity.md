# Pointer fields can refer to another heap allocation

A pointer loaded from one heap allocation is not constrained to point inside
that allocation. A modular store contract identifies its actual target.

```c filename=heap_pointer.c
struct holder { int32* target; };
void put(struct holder* h, int32* p) { h->target = p; }
int32 run() {
    int32* p = malloc(sizeof(int32));
    if (p == 0) { return -1; }
    struct holder* h = malloc(sizeof(struct holder));
    if (h == 0) { free(p); return -1; }
    put(h, p);
    int32 result = 0;
    if (h->target == p) { result = 1; }
    free(h);
    free(p);
    return result;
}
```

```click
verifying "heap_pointer.c";
void put(struct holder* h, int32* p) {
    owns uninitialized(h->target);
    ensures h->target == p;
    ensures defined(h->target);
}
int32 run() {
    ensures result == -1 or result == 1;
} by {
    step(); step();
    if p == 0 {
        step_until(function.exit);
    } else {
        step(); step(); step(); step();
        if h == 0 {
            step_until(function.exit);
        } else {
            step(); step();
            step(put, {});
            have defined(h->target) by { assumption(); }
            mark stored;
            step();
            have defined(h->target) by {
                transport(at(stored, defined(h->target)), defined(h->target)) using {
                    at(stored, defined(h->target));
                };
            }
            mark declared;
            step();
            have defined(h->target) by {
                transport(at(declared, defined(h->target)), defined(h->target)) using {
                    at(declared, defined(h->target));
                };
            }
            step_until(function.exit);
        }
    }
}
```

```expect
pass
```
