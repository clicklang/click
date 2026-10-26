# initialized aggregate globals and statics keep their first state

Positional compile-time initializers now populate supported struct globals and
function-local or file-scope `static` objects. Omitted scalar fields retain C's
zero initialization, and an external declaration observes the one initialized
definition across translation units.

```c filename=include/state.h
#ifndef STATE_H
#define STATE_H
struct state {
    int32 value;
    uint8 ready;
};
extern struct state shared;
int32 bump_shared();
#endif
```

```c filename=shared.c
#include "include/state.h"

struct state shared = {7, 1};

int32 bump_shared() {
    shared.value = shared.value + 1;
    return shared.value;
}
```

```c filename=private.c
#include "include/state.h"

static struct state file_private = {4, 1};

int32 increment_local() {
    static struct state local = {3};
    local.value = local.value + 1;
    return local.value;
}

int32 increment_file_private() {
    file_private.value = file_private.value + 1;
    return file_private.value;
}
```

```c filename=runner.c
#include "include/state.h"
int32 increment_local();
int32 increment_file_private();

int32 run() {
    bump_shared();
    bump_shared();
    increment_local();
    increment_local();
    return increment_file_private();
}
```

```click
verifying "shared.c";
verifying "private.c" as private_file;
verifying "runner.c";

int32 bump_shared() {
    requires shared.value < 1000;
    owns shared.value;
    ensures to_integer(result) == to_integer(old(shared.value) + 1);
    ensures to_integer(shared.value) == to_integer(old(shared.value) + 1);
}

int32 increment_local() {
    requires local.value > -1000;
    requires local.value < 1000;
    requires local.ready == 0;
    owns local.value;
    ensures to_integer(result) == to_integer(old(local.value) + 1);
    ensures to_integer(local.value) == to_integer(old(local.value) + 1);
    ensures local.ready == 0;
}

int32 increment_file_private() {
    requires file_private.value < 1000;
    owns file_private.value;
    ensures to_integer(result) == to_integer(old(file_private.value) + 1);
}

int32 run() {
    owns shared.value;
    owns private_file::increment_local::local.ready;
    owns private_file::increment_local::local.value;
    owns private_file::file_private.value;
    requires shared.value == 2;
    requires shared.value < 1000;
    requires private_file::increment_local::local.value == 3;
    requires private_file::increment_local::local.value > -1000;
    requires private_file::increment_local::local.value < 1000;
    requires private_file::increment_local::local.ready == 0;
    requires private_file::file_private.value == 4;
    ensures result == 5;
} by {
    have shared.value == 2 by solve();
    have shared.value < 1000 by solve();
    step();
    have shared.value == 3 by solve();
    have shared.value < 1000 by solve();
    step();
    have private_file::increment_local::local.value == 3 by solve();
    have private_file::increment_local::local.value > -1000 by solve();
    have private_file::increment_local::local.value < 1000 by solve();
    have private_file::increment_local::local.ready == 0 by solve();
    step();
    have private_file::increment_local::local.value == 4 by solve();
    have private_file::increment_local::local.value > -1000 by solve();
    have private_file::increment_local::local.value < 1000 by solve();
    have private_file::increment_local::local.ready == 0 by solve();
    step();
    have private_file::file_private.value < 1000 by solve();
    execute();
    solve();
}
```

```expect
pass
```
