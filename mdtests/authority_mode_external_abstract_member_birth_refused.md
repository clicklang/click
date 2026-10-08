# An assumed contract cannot create an authorized abstract member

`ticket` is an `authorized abstract resource`, so an assumed external contract
that produces one would change its population without authority. The call is
refused.

```c filename=external_abstract_member_birth.c
extern void mint(int32* p);
void caller(int32* p) { mint(p); }
```

```click resource_semantics=authority
authorized abstract resource ticket(p: int32*);

verifying "external_abstract_member_birth.c";

extern void mint(int32* p) {
    produces ticket(p);
}

void caller(int32* p) {
    produces ticket(p);
} by { execute(); simp(); }
```

```expect
fail: C calls are not yet supported by authority resource semantics
```
