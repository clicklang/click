# Arithmetic domains belong to a call's preconditions

```c filename=arithmetic_domains_call_precondition.c
int32 bounded(int32 x) { return demand_successor(x); }
```

```click
verifying "arithmetic_domains_call_precondition.c";
extern int32 demand_successor(int32 x) {
    requires to_integer(x + 1) > 0;
    ensures result == 0;
}
int32 bounded(int32 x) {
    requires 0 <= x;
    requires x < 2147483647;
    ensures result == 0;
}
```

```expect
pass
```
