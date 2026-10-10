# A refused 64-bit range names the field its bound is read from

`f` passes `s->data` and `s->len` to a callee that views
`data[0..len]`, but holds only the two fields, not the elements. The
refusal names the range the caller lacks as the caller would write it, with
its bound read from `s->len`, not as a load at the struct's address.

```c filename=a_refused_wide_range_names_its_bound_field.c
#include <stdint.h>
struct buf { uint64_t len; int32_t *data; };
int32_t first(int32_t *data, uint64_t len) { return data[0]; }
int32_t f(struct buf *s) { return first(s->data, s->len); }
```

```click
verifying "a_refused_wide_range_names_its_bound_field.c";
int32 first(int32* data, uint64 len) {
    requires 0u64 < len;
    views data[0..len];
} by { execute(); simp(); }
int32 f(struct buf* s) {
    views s->len;
    views s->data;
    requires 0u64 < s->len;
} by { execute(); simp(); }
```

```expect
fail: selected resource `views s->data[0u64..s->len]`
```
