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
  preserve by {
   have 0 <= old(n) - n + 1 by arithmetic() using { 0 <= n; n <= old(n); old(n) <= 15; n > 0; };
   have old(n) - n + 1 <= old(n) by arithmetic() using { 0 <= n; n <= old(n); old(n) <= 15; n > 0; };
   have 0 <= old(n) - n by arithmetic() using { 0 <= n; n <= old(n); old(n) <= 15; n > 0; };
   have old(n) - n <= 14 by arithmetic() using { 0 <= n; n <= old(n); old(n) <= 15; n > 0; };
   mark head;
   execute_until(back_edge());
   have p == at(head, p) + 1 by simp();
   have old(n) - n == (old(n) - at(head, n)) + 1 by arithmetic() using {
    at(head, n) > 0; at(head, n) <= old(n); old(n) <= 15;
   };
   have p == old(p) + (old(n) - n) by {
    rewrite(p == at(head, p) + 1);
    rewrite(old(n) - n == (old(n) - at(head, n)) + 1);
    arithmetic_certificate rules {
     premise 0: at(head, p) == old(p) + (old(n) - at(head, n)) => at(head, p) == old(p) + (old(n) - at(head, n));
     premise 1: 0 <= old(n) - at(head, n) => 0 <= old(n) - at(head, n);
     premise 2: old(n) - at(head, n) <= 14 => old(n) - at(head, n) <= 14;
     pointer_translation relation 0 bounds [1, 2] => at(head, p) + 1 == old(p) + ((old(n) - at(head, n)) + 1);
     conclusion 0;
    }
   }
   have 0 <= n by arithmetic() using { at(head, n) > 0; at(head, n) <= old(n); old(n) <= 15; };
   have n < at(head, n) by arithmetic() using { at(head, n) > 0; at(head, n) <= old(n); old(n) <= 15; };
   have n <= old(n) by arithmetic() using { at(head, n) > 0; at(head, n) <= old(n); old(n) <= 15; };
   close_invariants() by simp();
  }
 }
 execute(); simp();
}
```

```expect
pass
```
