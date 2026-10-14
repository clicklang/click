# owner buffer resource clauses

This checks the separation-logic guide's composite `owner_buffer` resource and
a contract that consumes memory, views memory, and consumes the composite.

```c filename=owner_buffer.c
struct owner {
    int32 len;
    int32* data;
};

int32 release_owner(int32* p, const int32* q, struct owner* owner) {
    return q[0];
}
```

```click
resource owner_buffer(owner: struct owner*) {
    owns owner[0..1];
    owns owner->data[0..owner->len];
    fact owner->len >= 0;
}

verifying "owner_buffer.c";

int32 release_owner(int32* p, const int32* q, struct owner* owner) {
    consumes p[0..1];
    views q[0..1];
    consumes owner_buffer(owner);

    ensures result == q[0] by auto;
}
```

```expect
pass
```
