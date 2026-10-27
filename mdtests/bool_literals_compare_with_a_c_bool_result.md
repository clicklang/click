# `true` and `false` compare with a C `bool` result

`true` and `false` are the literals of `Bool`, which a C `bool` denotes. A C
function returning `bool` can be specified with them, and a `Bool` value
written alone where a proposition is expected is the claim that it holds, so `ensures result;` and `ensures not result;` state the
same claims as `ensures result == true;` and `ensures result == false;`.

```c filename=bool_result.c
#include <stdbool.h>

bool is_positive(int x) { return x > 0; }
bool is_negative(int x) { return x < 0; }
```

```click
verifying "bool_result.c";

bool is_positive(int32 x) {
    requires x > 0;
    ensures result == true;
    ensures result;
    ensures result != false;
}

bool is_negative(int32 x) {
    requires x >= 0;
    ensures result == false;
    ensures not result;
}
```

```expect
pass
```
