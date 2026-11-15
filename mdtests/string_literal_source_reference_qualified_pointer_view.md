# Raised literal pointers retain a qualified byte view

```c filename=literal_view.c
const uint8* text() { return "ok"; }
```

```click
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "literal_view.c";
const uint8* text() {
    ensures result == text.string_literal(0) as (const uint8 *);
}
```

```expect
pass
```
