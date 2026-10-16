# a string function the C program uses brings its contracts and their predicates

`click::c::string` is not implicit. A C program that includes `<string.h>`
and calls `memset` brings that contract, and with it `click::bytes`, which
the contract is stated in, so the sidecar names `click::bytes::all_equal` without an
import. The negative twin is
[`string_predicates_need_an_import_without_a_string_function.md`](string_predicates_need_an_import_without_a_string_function.md).

```c filename=a_string_function_call_brings_the_c_string_contracts.c
#include <string.h>

int clear(unsigned char *d) {
    memset(d, 0, 4);
    return 0;
}
```

```click
target "x86_64-unknown-linux-gnu";
verifying "a_string_function_call_brings_the_c_string_contracts.c";

int32 clear(uint8 d[]) {
    owns d[0..4];
    requires click::bytes::all_equal(d, 0u64, 0u64, 0u8);
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
