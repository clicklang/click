# Generic pointer theorem parameters retain struct identity and stride

```c filename=objects.c
struct item { uint8 tag; int64 value; };
struct other { int32 a; int32 b; int32 c; };
void inspect(struct item *p, struct other *q, struct item **pp) {}
```

```click
verifying "objects.c";
import click::separation;

theorem identity<T>(p: T*) {
    ensures p == p by { normalize(); }
}
theorem nested<T>(p: T*, lo: int32, hi: int32, a: int32, b: int32) {
    requires lo <= a;
    requires a <= b;
    requires b <= hi;
    ensures contains(memory(p[lo..hi]), memory(p[a..b])) by {
        apply(separation::subrange(p, lo, hi, a, b)) using {
            lo <= a; a <= b; b <= hi;
        };
    }
}
theorem padded(p: struct item*) {
    ensures contains(memory(p[0..4]), memory(p[1..3])) by {
        apply(nested(p, 0, 4, 1, 3)) using {};
    }
}
void inspect(struct item *p, struct other *q, struct item **pp) {
    ensures true;
} by {
    have p == p by { apply(identity(p)) using {}; }
    have contains(memory(p[0..4]), memory(p[1..3])) by {
        apply(nested(p, 0, 4, 1, 3)) using {};
    }
    have contains(memory(q[0..4]), memory(q[1..3])) by {
        apply(nested(q, 0, 4, 1, 3)) using {};
    }
    have contains(memory(pp[0..4]), memory(pp[1..3])) by {
        apply(nested(pp, 0, 4, 1, 3)) using {};
    }
    have contains(memory((p as (int32 *))[0..4]), memory((p as (int32 *))[1..3])) by {
        apply(nested(p as (int32 *), 0, 4, 1, 3)) using {};
    }
    step_until(function.exit);
}
```

```expect
pass
```
