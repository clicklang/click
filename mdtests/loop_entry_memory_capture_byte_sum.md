# A moving cursor reads bytes from the captured loop footprint

The original `*p++` expression retains the pointer used for the read while
advancing the cursor. The proof carries the remaining view through each head,
checks signed addition without overflow, proves termination and a byte-sum
bound for every input of up to fifteen bytes, and preserves every input byte.
The count is the source program's remaining count; no processed counter is added.

```c filename=walk.c
int walk(const unsigned char *p, int n) {
    int total = 0;
    while (n > 0) {
        total += *p++;
        n--;
    }
    return total;
}
```

```click
verifying "walk.c";
theorem byte_as_int32(value: uint8) {
 ensures 0 <= value as int32 by { solve(); }
 ensures value as int32 <= 255 by { solve(); }
}

int32 walk(const uint8* p, int32 n) {
 requires 0 <= n and n <= 15;
 views p[0..n];
 ensures 0 <= result and result <= 3825;
 ensures forall (k: int32) { 0 <= k and k < old(n) implies old(p)[k] == old(p[k]) };
} by {
 step_until(loop(0));
 loop {
  decreases n;
  views p[0..n];
  invariant 0 <= n and n <= old(n);
  invariant 0 <= old(n) and old(n) <= 15;
  invariant p == old(p) + (old(n) - n);
  invariant viewable(p[0..n]);
  invariant 0 <= total and total <= 255 * (old(n) - n);
  preserve by {
   have 1 <= n by solve() using { n > 0; };
   have 0 <= to_integer(old(n) - n) by solve() using { n <= old(n); 0 <= n; old(n) <= 15; };
   have to_integer(old(n) - n + 1) <= to_integer(old(n)) by solve() using { 1 <= n; n <= old(n); 0 <= old(n); old(n) <= 15; };
   have defined(p[0]) by solve();
   mark before_pointer;
   step_until(assignment(total, 1));
   have __click_call_result0 == old(p) + (old(n) - n) by solve();
   have __click_call_result0 == at(before_pointer, p) by solve();
   have defined(__click_call_result0[0]) by solve();
   have viewable(__click_call_result0[0..1]) by solve();
   apply(byte_as_int32(__click_call_result0[0]));
   have to_integer(old(n) - n) <= 14 by solve() using { 1 <= n; n <= old(n); 0 <= old(n); old(n) <= 15; };
   have 255 * (old(n) - n) <= 3570 by solve() using { 1 <= n; n <= old(n); 0 <= old(n); old(n) <= 15; };
   have total <= 3570 by solve() using { total <= 255 * (old(n) - n); 255 * (old(n) - n) <= 3570; };
   have __click_call_result0[0] as int32 <= 255 by assumption();
   have to_integer(total) <= to_integer(2147483647 - __click_call_result0[0] as int32) by solve() using { total <= 3570; 0 <= __click_call_result0[0] as int32; __click_call_result0[0] as int32 <= 255; };
   have defined(total + (__click_call_result0[0] as int32));
   have defined(total + __click_call_result0[0] as int32) by solve();
   mark before_sum;
   step(); step();
   have to_integer(n) == to_integer(at(before_pointer, n) - 1) by solve();
   have n == at(before_pointer, n) - 1;
   have 0 <= n by solve() using { to_integer(n) == to_integer(at(before_pointer, n) - 1); 1 <= at(before_pointer, n); };
   have n <= old(n) by solve() using { to_integer(n) == to_integer(at(before_pointer, n) - 1); 1 <= at(before_pointer, n); at(before_pointer, n) <= old(n); };
   have to_integer(old(n) - n) == to_integer((old(n) - at(before_pointer, n)) + 1) by solve() using { to_integer(n) == to_integer(at(before_pointer, n) - 1); 0 <= n; n <= old(n); 0 <= old(n); old(n) <= 15; 1 <= at(before_pointer, n); at(before_pointer, n) <= old(n); };
   have p == at(before_pointer, p) + 1 by solve();
   have p == old(p) + (old(n) - n) by {
    rewrite(p == at(before_pointer, p) + 1);
    rewrite(to_integer(old(n) - n) == to_integer((old(n) - at(before_pointer, n)) + 1));
    arithmetic_certificate rules {
     premise 0: at(before_pointer, p) == old(p) + (old(n) - at(before_pointer, n)) => at(before_pointer, p) == old(p) + (old(n) - at(before_pointer, n));
     premise 1: 0 <= to_integer(old(n) - at(before_pointer, n)) => 0 <= to_integer(old(n) - at(before_pointer, n));
     premise 2: to_integer(old(n) - at(before_pointer, n)) <= 14 => to_integer(old(n) - at(before_pointer, n)) <= 14;
     pointer_translation relation 0 bounds [1, 2] => at(before_pointer, p) + 1 == old(p) + ((old(n) - at(before_pointer, n)) + 1);
     conclusion 0;
    }
   }
   have 0 <= to_integer(old(n) - n) by solve() using { 0 <= n; n <= old(n); 0 <= old(n); old(n) <= 15; 1 <= at(before_pointer, n); at(before_pointer, n) <= old(n); };
   have to_integer(old(n) - n + n) == to_integer(old(n)) by solve() using { 0 <= n; n <= old(n); 0 <= old(n); old(n) <= 15; };
   have viewable(p[0..n]) by solve();
   have total == at(before_sum, total) + at(before_sum, __click_call_result0[0] as int32);
   have 0 <= total by solve() using { total == at(before_sum, total) + at(before_sum, __click_call_result0[0] as int32); 0 <= at(before_sum, total); 0 <= at(before_sum, __click_call_result0[0] as int32); };
   have total <= 255 * (old(n) - n) by solve() using { total == at(before_sum, total) + at(before_sum, __click_call_result0[0] as int32); at(before_sum, total) <= 255 * (old(n) - at(before_sum, n)); n == at(before_pointer, n) - 1; at(before_sum, n) == at(before_pointer, n); at(before_sum, __click_call_result0[0] as int32) <= 255; };
  }
 }
 have n == 0 by solve() using { 0 <= n; n <= 0; };
 have 0 <= to_integer(old(n) - n) by solve() using { 0 <= old(n); old(n) <= 15; 0 <= n; n <= 0; n == 0; };
 have to_integer(old(n) - n) <= 15 by solve() using { 0 <= old(n); old(n) <= 15; 0 <= n; n <= 0; n == 0; };
 have 255 * (old(n) - n) <= 3825 by solve() using { 0 <= old(n); old(n) <= 15; 0 <= n; n <= 0; n == 0; };
 have total <= 3825 by solve() using { 0 <= total; total <= 255 * (old(n) - n); 255 * (old(n) - n) <= 3825; 0 <= old(n); old(n) <= 15; 0 <= n; n <= 0; n == 0; };
}
```

```expect
pass
```
