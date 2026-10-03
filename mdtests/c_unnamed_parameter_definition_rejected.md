# A function definition must name its parameters

Only a body-less prototype may omit a parameter name.

```c filename=c_unnamed_parameter_definition_rejected.c
int helper(int, int second) { return second; }

int32 run(int32 value) {
    return value;
}
```

```click
verifying "c_unnamed_parameter_definition_rejected.c";

int32 run(int32 value) {
    ensures result == value by auto;
}
```

```expect
fail:c_unnamed_parameter_definition_rejected.c:1: function definition `helper` has an unnamed parameter; only a body-less prototype may omit parameter names
```
