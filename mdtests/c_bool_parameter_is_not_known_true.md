# A `_Bool` parameter's range does not decide its value

The range fact a `bool` parameter carries is `flag == 0 or flag == 1`, of
its integer value; it does not make the parameter true. Without
`requires flag;`, the claim
`result == 1` stays unproved: the `flag == 0` case is a counterexample. See
`c_bool_parameter_range.md` for the claims the range does support.

```c filename=bool_not_true.c
#include <stdbool.h>

int present(bool flag) { return flag; }
```

```click
verifying "bool_not_true.c";

int32 present(bool flag) {
    ensures result == 1;
}
```

```expect
fail: `ensures result == 1` failed
```
