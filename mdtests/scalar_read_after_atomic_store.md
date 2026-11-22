# Reduced conditional array read

```c filename=probe.c
int32 immediate(int32 u) {
    int32 a[2];
    a[0] = 3;
    a[1] = 3;
    a[u] = 7;
    return a[0];
}
int32 later(int32 u) {
    int32 a[2];
    int32 r;
    a[0] = 3;
    a[1] = 3;
    a[u] = 7;
    r = 0;
    return a[0];
}
```

```click
import click::separation;
verifying "probe.c";
int32 immediate(int32 u) {
    requires 0 <= u;
    requires u < 2;
    ensures result == 3 or result == 7;
}
int32 later(int32 u) {
    requires 0 <= u;
    requires u < 2;
    ensures result == 3 or result == 7;
} by {
    step(); step(); step(); step();
    have a[0] == 3 by { known(); }
    mark before_store;
    step();
    have a[u] == 7 by { known(); }
    have a[0] == 3 or a[0] == 7 by {
        if u == 0 {
            have a[0] == 7 by { normalize() using { a[u] == 7; u == 0; }; }
            known();
        } else {
            have separate(memory(a[u]), memory(a[0])) by {
                apply(separation::separate_elements(a, u, 0));
            }
            have separate(statement(4).footprint, memory(a[0])) by {
                solve() using { separate(memory(a[u]), memory(a[0])); };
            }
            have a[0] == at(before_store, a[0]) by {
                preserve(memory(a[0]), statement(4));
            }
            have a[0] == 3 by { rewrite(a[0], at(before_store, a[0])); known(); }
            known();
        }
    }
    mark stored;
    step();
    have a[0] == at(stored, a[0]) by { known(); }
    step();
    solve();
}
```

```expect
pass
```
