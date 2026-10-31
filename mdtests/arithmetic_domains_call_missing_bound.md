# The caller must establish arithmetic definedness in a precondition

```c filename=arithmetic_domains_call_missing_bound.c
int32 unbounded(int32 x) { return demand_successor(x); }
```

```click
verifying "arithmetic_domains_call_missing_bound.c";
extern int32 demand_successor(int32 x) {
    requires to_integer(x + 1) > 0;
    ensures result == 0;
}
int32 unbounded(int32 x) {
    requires 0 <= x;
    ensures result == 0;
}
```

```expect
fail: x <= 2147483646
```
