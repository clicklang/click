# Callback typedef aliases retain const struct-pointer signatures

```c filename=callback.h
struct item { int value; };
typedef const struct item *(*view_t)(const struct item *);
typedef view_t view_alias_t;
const struct item *view(const struct item *p);
```

```c filename=view.c
#include "callback.h"
const struct item *view(const struct item *p) { return p; }
```

```c filename=caller.c
#include "callback.h"
const struct item *relay(const struct item *p) {
    view_alias_t callback = &view;
    return callback(p);
}
int read_view(const struct item *p) {
    view_alias_t callback = &view;
    const struct item *result = callback(p);
    return result->value;
}
```

```click
verifying "view.c";
verifying "caller.c";
const struct item *view(const struct item *p) {
    ensures result == p;
} by { execute(); simp(); }
const struct item *relay(const struct item *p) {
    ensures result == p;
} by { execute(); simp(); }
int read_view(const struct item *p) {
    views p->value;
    ensures result == p->value;
} by { execute(); simp(); }
```

```expect
pass
```
