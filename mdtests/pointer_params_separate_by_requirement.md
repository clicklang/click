# a `separate(...)` requirement keeps a write through one pointer off another

The C of `pointer_params_may_alias_without_separate.md`, with the non-overlap
stated directly as a requirement: `separate(memory(dst[0..1]), memory(src[0..1]))`
lets the write through `dst` preserve `src[0]`.

```c filename=pointer_params_separate_by_requirement.c
int32 clobber_dst(int32* dst, int32* src) {
    dst[0] = 1;
    return src[0];
}
```

```click
verifying "pointer_params_separate_by_requirement.c";

int32 clobber_dst(int32* dst, int32* src) {
    consumes dst[0..1];
    views src[0..1];
    requires separate(memory(dst[0..1]), memory(src[0..1]));

    ensures source_unchanged: src[0] == old(src[0]) by auto;
}
```

```expect
pass
```
