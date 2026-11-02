# Byte facts from before a write cannot reconstruct the old word afterwards

```c filename=stale_bytes.c
unsigned int rewrite(unsigned int *p) {
    *p = 1;
    return *p;
}
```

```click
verifying "stale_bytes.c";
import click::integer;
uint32 rewrite(uint32* p) {
    owns p[0..1];
    requires p[0] == 0u32;
    ensures result == 0u32;
} by {
    apply(integer::uint32_from_le_bytes(p));
    step_until(function.exit);
}
```

```expect
fail: unclosed goal
```
