# A symbolic return boundary uses its explicit frame proof

The returned middle range has two symbolic neighbors. Its separation proof
names the complete retained footprint; return admission checks that retained
proof directly rather than searching the frame or its aliases.

```c filename=symbolic_frame_proof.c
void acquire_middle(int *p, int n, int m);
void forward(int *p, int n, int m) { acquire_middle(p, n, m); }
```

```click
import click::separation;
verifying "symbolic_frame_proof.c";
extern void acquire_middle(int32* p, int32 n, int32 m) {
    produces p[n..m];
}
void forward(int32* p, int32 n, int32 m) {
    requires 0 < n;
    requires n < m;
    requires m < 16;
    owns p[0..n];
    owns p[m..16];
    produces p[n..m];
} by {
    have 0 <= n by { solve(); }
    have n <= m by { solve(); }
    have m <= 16 by { solve(); }
    have separate(memory(p[0..n]), memory(p[n..m])) by {
        apply(separation::separate_adjacent_ranges(p, 0, n, m)) using { 0 <= n; n <= m; };
    }
    have separate(memory(p[n..m]), memory(p[m..16])) by {
        apply(separation::separate_adjacent_ranges(p, n, m, 16)) using { n <= m; m <= 16; };
    }
    have separate(memory(p[m..16]), memory(p[n..m])) by {
        apply(separation::separate_symm(memory(p[n..m]), memory(p[m..16]))) using {
            separate(memory(p[n..m]), memory(p[m..16]));
        };
    }
    have separate(memory(p[0..n]) * memory(p[m..16]), memory(p[n..m])) by {
        apply(separation::separate_star(memory(p[0..n]), memory(p[m..16]), memory(p[n..m]))) using {
            separate(memory(p[0..n]), memory(p[n..m]));
            separate(memory(p[m..16]), memory(p[n..m]));
        };
    }
    have separate(memory(p[n..m]), memory(p[0..n]) * memory(p[m..16])) by {
        apply(separation::separate_symm(memory(p[0..n]) * memory(p[m..16]), memory(p[n..m]))) using {
            separate(memory(p[0..n]) * memory(p[m..16]), memory(p[n..m]));
        };
    }
    step();
}
```

```expect
pass
```
