# Input initialization is a fact about entry, not memory after free

```c filename=free_input.c
void f(int32 *p, int32 n) { free(p); }
```
```click
verifying "free_input.c";
void f(int32 *p, int32 n) {
    requires 0 < n;
    requires n < 100;
    consumes allocation(p, n * 4);
    consumes p[0..n];
} by {
    have forall (j: int32) { 0 <= j and j < n implies defined(p[j]) } by { known(); }
    step();
    have forall (j: int32) { 0 <= j and j < n implies defined(p[j]) } by { known(); }
}
```
```expect
fail: `known`
```
