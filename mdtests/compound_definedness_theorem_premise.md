# Compound definedness satisfies a theorem's instantiated guard conjunction

The standard addition bridge takes a compound first argument. Its required
inner and outer overflow guards are both held, even if the checked fact store
has decomposed their conjunction. Explicit evidence lists use the same rule.

```c filename=compound_guard.c
int32 probe(int32 a, int32 b, int32 c) { return 0; }
```

```click
import click::integer;

verifying "compound_guard.c";

theorem bridge(a: int32, b: int32, c: int32) {
    requires defined(a + b + c);
    ensures to_integer(a + b + c) == to_integer(a + b) + to_integer(c) by {
        apply(int32_add_to_integer(a + b, c));
        assumption();
    }
}

int32 probe(int32 a, int32 b, int32 c) {
    requires defined(a + b + c);
    ensures result == 0;
} by {
    have to_integer(a + b + c) == to_integer(a + b) + to_integer(c) by {
        apply(int32_add_to_integer(a + b, c)) using { defined(a + b + c); };
        assumption();
    }
    apply(bridge(a, b, c)) using { defined(a + b + c); };
    execute(); simp();
}
```

```expect
pass
```
