# `arithmetic() using` substitutes listed equalities

An equality premise bounds its atom on both sides, so `x == 5` proves `x - 1`
defined and closes `x - 1 == 4`. Equalities whose own operations need
bounds convert in turn, `a == b + 1` before `c == a + 1`, and a bound
substitutes through each of them to the listed bound on `b`.

```c filename=arithmetic_using_chains_equalities.c
int32 constant(int32 x) { return 0; }
int32 offset(int32 a, int32 b, int32 c) { return 0; }
int32 bounded(int32 a, int32 b, int32 c) { return 0; }
```

```click
verifying "arithmetic_using_chains_equalities.c";
int32 constant(int32 x) {
    requires x == 5;
    ensures x - 1 == 4;
} by { execute(); arithmetic() using { x == 5; }; }
int32 offset(int32 a, int32 b, int32 c) {
    requires c == a + 1;
    requires a == b + 1;
    requires 0 <= b;
    requires b <= 500;
    ensures c - 2 == b;
} by { execute(); arithmetic() using { c == a + 1; a == b + 1; 0 <= b; b <= 500; }; }
int32 bounded(int32 a, int32 b, int32 c) {
    requires c == a + 1;
    requires a == b + 1;
    requires 0 <= b;
    requires b <= 500;
    ensures c <= 502;
} by { execute(); arithmetic() using { c == a + 1; a == b + 1; 0 <= b; b <= 500; }; }
```

```expect
pass
```
