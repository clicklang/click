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
import click::integer;
import click::separation;
verifying "walk.c";
theorem byte_as_int32(value: uint8) {
 ensures 0 <= value as int32 by { solve(); }
 ensures value as int32 <= 255 by { solve(); }
}

theorem contains_cursor_range(base: const uint8*, offset: int32, limit: int32, remaining: int32) {
 requires 0 <= offset;
 requires offset <= limit;
 requires 0 <= remaining;
 requires remaining <= limit - offset;
 ensures contains(memory(base[0..limit]), memory((base + offset)[0..remaining])) by {
  apply(separation::contains_subrange(base, 0, limit, offset, limit));
  apply(separation::contains_rebase(base, offset, limit));
  apply(separation::contains_subrange(base + offset, 0, limit - offset, 0, remaining));
  apply(separation::contains_trans(memory(base[offset..limit]), memory((base + offset)[0..limit - offset]), memory((base + offset)[0..remaining])));
  apply(separation::contains_trans(memory(base[0..limit]), memory(base[offset..limit]), memory((base + offset)[0..remaining])));
 }
}

int32 walk(const uint8* p, int32 n) {
 requires 0 <= n and n <= 15;
 views p[0..n];
 ensures 0 <= result and result <= 3825;
 ensures forall (k: int32) { 0 <= k and k < old(n) implies old(p)[k] == old(p[k]) };
} by {
 step_until(loop(0).entry);
 // Declaring and initializing total leaves the input bytes defined.
 have forall (j: int32) { 0 <= j and j < n implies defined(p[j]) } by {
  intro(); intro();
  instantiate(forall (k: int32) { 0 <= k and k < n implies defined(old(p[k])) }, j);
  have separate(memory(total), memory(p[j])) by { known(); }
  have separate(statement(0).region(0).footprint, memory(p[j])) by {
   solve() using { separate(memory(total), memory(p[j])); };
  }
  have at(statement(0).region(0).exit, defined(p[j])) by {
   preserve(memory(p[j]), statement(0).region(0));
  }
  have separate(statement(0).region(1).footprint, memory(p[j])) by {
   solve() using { separate(memory(total), memory(p[j])); };
  }
  have defined(p[j]) by {
   preserve(memory(p[j]), statement(0).region(1));
  }
  known();
 }
 loop {
  decreases n;
  views p[0..n];
  invariant 0 <= n and n <= old(n);
  invariant 0 <= old(n) and old(n) <= 15;
  invariant p == old(p) + (old(n) - n);
  invariant viewable(p[0..n]);
  invariant forall (k: int32) { 0 <= k and k < n implies defined(p[k]) };
  invariant 0 <= total and total <= 255 * (old(n) - n);
  maintain by {
   have 1 <= n by solve() using { n > 0; };
   have 0 <= to_integer(old(n) - n) by solve() using { n <= old(n); 0 <= n; old(n) <= 15; };
   have to_integer(old(n) - n + 1) <= to_integer(old(n)) by solve() using { 1 <= n; n <= old(n); 0 <= old(n); old(n) <= 15; };
   have defined(p[0]) by {
    instantiate(forall (k: int32) { 0 <= k and k < n implies defined(p[k]) }, 0);
    have 0 < n by { known(); }
    known();
   }
   apply(separation::contains_subrange(p, 0, n, 0, 1));
   apply(separation::viewable_restrict(memory(p[0..n]), memory(p[0..1])));
   have separate(memory(total), memory(old(p)[0..old(n)])) by { known(); }
   have n <= old(n) - (old(n) - n) by {
    solve() using { 0 <= n; n <= old(n); 0 <= old(n); old(n) <= 15; };
   }
   apply(contains_cursor_range(old(p), old(n) - n, old(n), n));
   have contains(memory(old(p)[0..old(n)]), memory(p[0..n])) by {
    rewrite(p, old(p) + (old(n) - n));
    known();
   }
   apply(separation::contains_refl(memory(total)));
   apply(separation::separate_restrict(memory(total), memory(old(p)[0..old(n)]), memory(total), memory(p[0..n])));
   mark before_pointer;
   step_until(assignment(total, 1).entry);
   have at(before_pointer, p) == old(p) + (old(n) - n) by solve();
   have defined(at(before_pointer, p[0])) by solve();
   have at(before_pointer, viewable(p[0..1])) by { known(); }
   apply(byte_as_int32(at(before_pointer, p[0])));
   have to_integer(old(n) - n) <= 14 by solve() using { 1 <= n; n <= old(n); 0 <= old(n); old(n) <= 15; };
   have 255 * (old(n) - n) <= 3570 by solve() using { 1 <= n; n <= old(n); 0 <= old(n); old(n) <= 15; };
   have total <= 3570 by solve() using { total <= 255 * (old(n) - n); 255 * (old(n) - n) <= 3570; };
   have at(before_pointer, p[0] as int32) <= 255 by known();
   have to_integer(total) <= to_integer(2147483647 - at(before_pointer, p[0] as int32)) by solve() using { total <= 3570; 0 <= at(before_pointer, p[0] as int32); at(before_pointer, p[0] as int32) <= 255; };
   have defined(total + (at(before_pointer, p[0] as int32)));
   have defined(total + at(before_pointer, p[0] as int32)) by solve();
   mark before_sum;
   step(); step();
   have to_integer(n) == to_integer(at(before_pointer, n) - 1) by solve();
   have n == at(before_pointer, n) - 1;
   have 0 <= n by solve() using { to_integer(n) == to_integer(at(before_pointer, n) - 1); 1 <= at(before_pointer, n); };
   have n <= old(n) by solve() using { to_integer(n) == to_integer(at(before_pointer, n) - 1); 1 <= at(before_pointer, n); at(before_pointer, n) <= old(n); };
   have to_integer(old(n) - n) == to_integer((old(n) - at(before_pointer, n)) + 1) by solve() using { to_integer(n) == to_integer(at(before_pointer, n) - 1); 0 <= n; n <= old(n); 0 <= old(n); old(n) <= 15; 1 <= at(before_pointer, n); at(before_pointer, n) <= old(n); };
   have p == at(before_pointer, p) + 1 by solve();
   have p == old(p) + (old(n) - n) by {
    rewrite(p, at(before_pointer, p) + 1);
    rewrite(to_integer(old(n) - n), to_integer((old(n) - at(before_pointer, n)) + 1));
    solve() using { at(before_pointer, p) == old(p) + (old(n) - at(before_pointer, n)); 0 <= to_integer(old(n) - at(before_pointer, n)); to_integer(old(n) - at(before_pointer, n)) <= 14; };
   }
   have 0 <= to_integer(old(n) - n) by solve() using { 0 <= n; n <= old(n); 0 <= old(n); old(n) <= 15; 1 <= at(before_pointer, n); at(before_pointer, n) <= old(n); };
   have to_integer(old(n) - n + n) == to_integer(old(n)) by solve() using { 0 <= n; n <= old(n); 0 <= old(n); old(n) <= 15; };
   // Preserve the pre-increment span across the sum store, then take its suffix.
   have separate(loop(0).statement(0).region(1).footprint, at(before_pointer, memory(p[0..n]))) by {
    solve() using { at(before_pointer, separate(memory(total), memory(p[0..n]))); };
   }
   have viewable(at(before_pointer, memory(p[0..n]))) by {
    preserve(at(before_pointer, memory(p[0..n])), loop(0).statement(0).region(1));
   }
   have 1 <= at(before_pointer, n) by { known(); }
   apply(separation::contains_subrange(at(before_pointer, p), 0, at(before_pointer, n), 1, at(before_pointer, n)));
   apply(separation::contains_rebase(at(before_pointer, p), 1, at(before_pointer, n)));
   have contains(memory(at(before_pointer, p)[1..at(before_pointer, n)]), memory(p[0..n])) by { known(); }
   apply(separation::contains_trans(at(before_pointer, memory(p[0..n])),
     memory(at(before_pointer, p)[1..at(before_pointer, n)]), memory(p[0..n])));
   apply(separation::viewable_restrict(at(before_pointer, memory(p[0..n])), memory(p[0..n])));
   have total == at(before_sum, total) + at(before_pointer, p[0] as int32);
   have 0 <= total by solve() using { total == at(before_sum, total) + at(before_pointer, p[0] as int32); 0 <= at(before_sum, total); 0 <= at(before_pointer, p[0] as int32); };
   have total <= 255 * (old(n) - n) by solve() using { total == at(before_sum, total) + at(before_pointer, p[0] as int32); at(before_sum, total) <= 255 * (old(n) - at(before_sum, n)); n == at(before_pointer, n) - 1; at(before_sum, n) == at(before_pointer, n); at(before_pointer, p[0] as int32) <= 255; };
   // Byte k at the new cursor is byte k + 1 at the saved cursor.
   have forall (k: int32) { 0 <= k and k < n implies defined(p[k]) } by {
    intro(); intro();
    have k < 2147483647 by { solve() using { k < n; n <= old(n); old(n) <= 15; }; }
    apply(integer::int32_increment_below_max_is_defined(k));
    apply(integer::int32_add_to_integer(k, 1));
    have 0 <= to_integer(k) + 1 by { solve() using { 0 <= k; }; }
    have to_integer(k) + 1 < to_integer(at(before_pointer, n)) by {
     solve() using { k < n; n == at(before_pointer, n) - 1; };
    }
    have 0 <= (k + 1) and k + 1 < at(before_pointer, n) by {
     rewrite(to_integer(k + 1), to_integer(k) + 1);
     known();
    }
    instantiate(at(before_pointer, forall (j: int32) { 0 <= j and j < n implies defined(p[j]) }), k + 1);
    have at(before_pointer, defined(p[k + 1])) by { known(); }
    have p + 0 == at(before_pointer, p) + 1 by { known(); }
    have to_integer(k) - 0 == to_integer(k + 1) - to_integer(1) by {
     rewrite(to_integer(k + 1), to_integer(k) + 1);
     known();
    }
    apply(integer::uint8_pointer_translate_int32(p, at(before_pointer, p), 0, 1, k, k + 1));
    have &p[k] == at(before_pointer, &p[k + 1]) by { known(); }
    have separate(memory(total), memory(p[k])) by { known(); }
    have at(before_sum, defined(p[k])) by {
     rewrite(&p[k], at(before_pointer, &p[k + 1]));
     known();
    }
    have separate(loop(0).statement(0).region(1).footprint, memory(p[k])) by {
     solve() using { separate(memory(total), memory(p[k])); };
    }
    have defined(p[k]) by { preserve(memory(p[k]), loop(0).statement(0).region(1)); }
   }
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
