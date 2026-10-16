# auto reads a call postcondition for a machine bound

Under `arithmetic "integer";` the callee's `ensures result == x + 1;` is an
Integer fact at the call site, while the caller's `ensures result <= 50;`
compares a machine value with a constant. `auto` proves the machine bound
through its Integer reading, `to_integer(result) <= 50`, citing the callee's
postcondition and the caller's requirements; the Integer fact then supplies
the native bound.

```c filename=auto_reads_a_call_postcondition_for_a_machine_bound.c
int inc(int x) { return x + 1; }
int g(int y) { int a = inc(y); return a; }
```

```click
arithmetic "integer";
verifying "auto_reads_a_call_postcondition_for_a_machine_bound.c";

int32 inc(int32 x) {
    requires x < 100;
    requires 0 <= x;
    ensures result == x + 1;
}

int32 g(int32 y) {
    requires 0 <= y;
    requires y < 50;
    ensures result <= 50;
}
```

```expect
pass
```
