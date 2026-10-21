# instantiate using names its missing premise

A refused `instantiate ... using` in a pure theorem spells the instantiated
premise it lacks with the theorem's parameter names.

```c filename=instantiate_using_names_its_missing_premise.c
void unused(void) {}
```

```click
verifying "instantiate_using_names_its_missing_premise.c";

function f(a: int32) -> int32 { a }

theorem t(x: int32, n: int32) {
    requires forall (k: int32) { 0 <= k and k < n implies f(k) == 0 };
    requires 0 <= x;
    requires x < n;
    ensures f(x) == 0 by {
        instantiate(forall (k: int32) { 0 <= k and k < n implies f(k) == 0 }, x) using { 0 <= x; };
    }
}
```

```expect
fail: instantiated premise `x < n` does not follow from the listed evidence
```
