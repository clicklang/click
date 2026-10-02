# A non-inline `static` function definition in a header stays rejected

Source-bundle headers accept only `static inline` helper bodies.

```c filename=include/helper.h
static int add_one(int value) {
    return value + 1;
}
```

```c filename=c_static_function_in_header_rejected.c
#include "include/helper.h"

int32 run(int32 value) {
    return value;
}
```

```click
verifying "c_static_function_in_header_rejected.c";

int32 run(int32 value) {
    ensures result == value by auto;
}
```

```expect
fail:include/helper.h:1
```
