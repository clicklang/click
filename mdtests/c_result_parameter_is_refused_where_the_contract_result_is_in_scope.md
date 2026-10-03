# `c(result)` is refused where the contract result is in scope

The kernel's exit state holds the return value under the name `result`, so a
postcondition cannot read a C parameter spelled `result` through `c(result)`.
Reading it there used to give the return value, which proved this false claim
about the parameter for every input. The claim is now refused with the
spelling to use instead.

```c filename=c_result_parameter_seven.c
int32 seven(int32 result) {
    return 7;
}
```

```click
verifying "c_result_parameter_seven.c";

int32 seven(int32 result) {
    requires 0 <= c(result) and c(result) <= 100;
    ensures c(result) == 7;
}
```

```expect
fail: `c(result)` cannot name a C binding where the contract `result` is in scope
```
