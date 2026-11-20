# A bare `with` proves several closing body facts

`control(obj)` carries two body facts. After the block runs to function exit,
the closing fold leaves both open: the facts were established at entry, and
reaching the exit takes more than one step. Without a written `by`, the
implicit closer proves each, and expansion writes them as `have`s at the end
of the block.

```c filename=a_bare_open_proves_several_closing_facts.c
struct child {
    int32 refs;
    int32 payload;
};

int32 read_payload(struct child* c) {
    struct child* kid = c;
    int32 value = kid->payload;
    return value;
}
```

```click
resource control(obj: struct child*) {
    owns *obj;
    fact defined(obj->refs);
    fact defined(obj->payload);
}

verifying "a_bare_open_proves_several_closing_facts.c";

int32 read_payload(struct child* c) {
    owns control(c);
    ensures result == c->payload;
} by {
    with(control(c)) { step_until(function.exit); }
    solve();
}
```

```expect
pass
```
