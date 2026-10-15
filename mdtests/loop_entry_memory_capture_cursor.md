# A moving cursor retains the loop-entry footprint

Both pointer and count are modified. The ordinary views clause still acquires
the original physical range; it does not claim a new range at each cursor.

```c filename=cursor.c
int cursor(const unsigned char *p, int n) { while (n > 0) { p++; n--; } return n; }
```

```click
verifying "cursor.c";
int32 cursor(const uint8* p, int32 n) {
 requires 0 <= n and n <= 15;
 views p[0..n];
 ensures result == 0;
} by {
 loop {
  decreases n;
  views p[0..n];
  invariant 0 <= n and n <= old(n);
  invariant p == old(p) + (old(n) - n);
  invariant pointer_origin(p, old(p) + (old(n) - n));
  preserve by {
   have 0 <= old(n) - n + 1 by {
    arithmetic() using { 0 <= n; n <= old(n); old(n) <= 15; n > 0; }
   }
   have old(n) - n + 1 <= old(n) by {
    arithmetic() using { 0 <= n; n <= old(n); old(n) <= 15; n > 0; }
   }
   step();
   step();
   have 0 <= n and n <= 15 by { simp(); }
   have at(statement(1).entry, n) <= 15 by { simp(); }
   have p == old(p) + (old(n) - n) by {
    arithmetic() using {
     at(statement(1).entry, p) == old(p) + (old(n) - at(statement(1).entry, n));
     at(statement(1).entry, n) > 0;
     at(statement(1).entry, n) <= old(n);
     old(n) <= 15;
     0 <= n;
     n <= 15;
     at(statement(1).entry, n) <= 15;
     0 <= old(n);
    }
   }
   close_invariants by simp;
  }
 }
 execute(); simp();
}
```

```expect
pass
```
