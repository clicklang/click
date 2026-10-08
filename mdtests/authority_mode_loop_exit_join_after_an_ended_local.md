# Loop exits join after one of them ends an address-taken local in authority mode

One exit of `inner_addr` declares `inner`, takes its address and writes
through it before breaking. The other exit never declares it. When the first
exit breaks, `inner`'s lifetime ends, so both exits leave the same storage
behind.

Under authority semantics each storage transition mints a fresh identity for
the creation ledger. The two exits therefore held ledgers that record the same
state under different names, and the loop join refused them with "loop exits
reach different states ... the symbolic state". The join now compares the
recorded ledger state. It still compares every other component exactly.

```c filename=inner_addr.c
int32 inner_addr(int32 flag) {
    int32 kept = 0;
    while (true) {
        if (flag == 0) {
            int32 inner = 5;
            int32* q = &inner;
            *q = 6;
            break;
        }
        break;
    }
    return kept;
}
```

```click resource_semantics=authority
verifying "inner_addr.c";

int32 inner_addr(int32 flag) {
    ensures result == 0;
} by {
    step();
    step();
    loop {
        decreases 0;
        preserve by {
            if flag == 0 {
                step();
                step();
                step();
                step();
                step();
                step();
                step();
            } else {
                step();
                step();
                step();
            }
        }
    }
    step();
    simp();
}
```

```expect
pass
```
