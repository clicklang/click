# Explicit containment restricts viewability

```c filename=first.c
int first(int *p, int n, int a, int b) { return p[0]; }
```

```click
import click::separation;
verifying "first.c";
int32 first(int32* p, int32 n, int32 a, int32 b) {
    requires 1 <= n;
    requires 0 <= a;
    requires a <= b;
    requires b <= n;
    views p[0..n];
    ensures result == p[0];
} by {
    have contains(memory(p[0..n]), memory(p[a..b])) by {
        apply(separation::subrange(p, 0, n, a, b)) using {
            0 <= a;
            a <= b;
            b <= n;
        };
    }
    have viewable(p[a..b]) by {
        apply(separation::viewable_restrict(memory(p[0..n]), memory(p[a..b]))) using {
            viewable(p[0..n]);
            contains(memory(p[0..n]), memory(p[a..b]));
        };
    }
    step();
    assumption();
}
```

```expect
pass
```
