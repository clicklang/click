# The kernel target rejects user-space system headers

The `kernel` mode has no `<stddef.h>` or `<pthread.h>` model, so
this source is rejected under it. The same source verifies under
`target "x86_64-unknown-linux-gnu";` (`mdtests/userspace_target_directive.md`).

```c filename=null_pointer.c
#include <stddef.h>
#include <pthread.h>

int32_t is_null(int32_t* p) {
    return p == NULL;
}
```

```click
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "null_pointer.c";

int32 is_null(int32* p) {
    requires p == 0;
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: system header `<stddef.h>` is not supported for x86_64-unknown-linux-gnu (kernel); Click models it for `x86_64-unknown-linux-gnu (userspace)`, selected with `mode "userspace";` in the sidecar
```
