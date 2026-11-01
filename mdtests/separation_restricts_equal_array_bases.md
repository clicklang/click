# Restrict separation after an explicit address equality

```click
import click::separation;
theorem selected(A: Resource, p: int32*, q: int32*, i: int32, cap: int32) {
    requires p == q;
    requires separate(A, memory(p[0..cap]));
    requires 0 <= i;
    requires i < cap;
    ensures separate(A, memory(q[i])) by {
        have separate(A, memory(q[0..cap])) by {
            rewrite(q == p);
            assumption();
        }
        have i <= 2147483646 by { solve() using { i < cap; }; }
        have defined(i + 1) by { solve() using { 0 <= i; i <= 2147483646; }; }
        have i <= ((i + 1) as int32) by { solve() using { 0 <= i; i < cap; }; }
        have ((i + 1) as int32) <= cap by { solve() using { 0 <= i; i < cap; }; }
        have contains(memory(q[0..cap]), memory(q[i..i+1])) by {
            apply(separation::subrange(q, 0, cap, i, i+1)) using {
                defined(i + 1); 0 <= i; i <= ((i+1) as int32); ((i+1) as int32) <= cap;
            };
        }
        have contains(A, A) by { normalize(); }
        have separate(A, memory(q[i..i+1])) by {
            apply(separation::restrict(A, memory(q[0..cap]), A, memory(q[i..i+1]))) using {
                defined(i + 1); separate(A, memory(q[0..cap])); contains(A, A);
                contains(memory(q[0..cap]), memory(q[i..i+1]));
            };
        }
        have contains(memory(q[i..i+1]), memory(q[i])) by { normalize(); }
        apply(separation::restrict(A, memory(q[i..i+1]), A, memory(q[i]))) using {
            defined(i + 1); separate(A, memory(q[i..i+1])); contains(A, A);
            contains(memory(q[i..i+1]), memory(q[i]));
        };
    }
}
```

```expect
pass
```
