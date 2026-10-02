# A prototype may leave its parameters unnamed

Parameter names in a body-less prototype have no meaning in C. The unnamed
prototype is compatible with the named definition that follows, and an
unnamed external prototype takes its contract from the sidecar as usual.

```c filename=include/api.h
extern int pick(int, const int *);
extern int outside(int, int *);
```

```c filename=c_unnamed_prototype_parameters.c
#include "include/api.h"

int pick(int value, const int *unused) {
    return value;
}

int32 run(int32 value) {
    return outside(pick(value, 0), 0);
}
```

```click
verifying "c_unnamed_prototype_parameters.c";

extern int32 outside(int32 code, int32* out) {
    ensures result == code;
}

int32 pick(int32 value, const int32* unused) {
    ensures result == value by auto;
}

int32 run(int32 value) {
    ensures result == value by auto;
}
```

```expect
pass
```
