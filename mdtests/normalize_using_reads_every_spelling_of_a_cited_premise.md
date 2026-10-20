# normalize using reads every spelling of a cited premise

A cited premise decides the goal's conditions in any of its spellings, in
every family: at the other polarity, mirrored, and, for a comparison with a
constant, from cited conditions on the same term. An ambient equality between
C machine values decides a condition at either width.

```c filename=normalize_using_reads_every_spelling_of_a_cited_premise.c
void unused(void) {}
```

```click
verifying "normalize_using_reads_every_spelling_of_a_cited_premise.c";

theorem spellings(x: int32, y: int32, a: uint64, b: uint64, n: int32) {
    requires x < y;
    requires a < b;
    requires n == 0;
    ensures not (x >= y) by { normalize() using { x < y; }; }
    ensures b > a by { normalize() using { a < b; }; }
    ensures n != 1 by { normalize() using { n == 0; }; }
}

theorem integer_mirror(i: Integer, j: Integer) {
    requires i < j;
    ensures (if j > i { 1 } else { 2 }) == 1 by { normalize() using { i < j; }; }
}

theorem ambient_wide(a: uint64, b: uint64) {
    requires a == b;
    ensures a == b by { normalize() using { }; }
}
```

```expect
pass
```
