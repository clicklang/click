# Nested loops retain input authority through proved cursor aliases

The inner loop calls a checked reader through the abstract outer cursor.
A checked pointer equality and input subrange carry its byte view and stable
borrow binding into the nested loop. The input bytes are unchanged.

```c filename=alias-nested-call.c
int32 read(const uint8* p) { return p[0]; }
int32 f(const uint8* bytes) { const uint8* cursor = bytes; int32 outer = 0; while (outer < 2) { const uint8* chunk = cursor; int32 inner = 1; while (inner > 0) { int32 value = read(chunk); inner -= 1; } cursor += 4; outer += 1; } return 0; }
```

```click
import click::separation;
verifying "alias-nested-call.c";
int32 read(const uint8* p) { views p[0..4]; ensures 0 <= result and result <= 255; }
int32 f(const uint8* bytes) { views bytes[0..8]; ensures result == 0; } by {
 step_until(loop(0).entry);
 have viewable(bytes[0..8]) by { observe(bytes[0..8]); }
 loop {
 decreases 2 - outer;
 views bytes[0..8];
 invariant 0 <= outer and outer <= 2;
 invariant cursor == bytes + (4 * outer);
 invariant bytes == old(bytes);
 invariant viewable(bytes[0..8]);
 maintain by {
  have outer < 2;
  mark outer_head;
  step_until(loop(1).entry);
  have chunk == bytes + (4 * outer);
  have 0 <= to_integer(4 * outer) by { close() using { 0 <= outer; outer < 2; }; }
  have to_integer(4 * outer) <= 4 by { close() using { 0 <= outer; outer < 2; }; }
  have to_integer(4 * outer + 4) <= 8 by { close() using { 0 <= outer; outer < 2; }; }
  have to_integer(4 * outer) <= to_integer(4 * outer + 4) by { close() using { 0 <= outer; outer < 2; }; }
  have viewable(bytes[0..8]) by { observe(bytes[0..8]); }
  have contains(memory(bytes[0..8]), memory(bytes[4 * outer..4 * outer + 4])) by {
   apply(separation::contains_subrange(bytes, 0, 8, 4 * outer, 4 * outer + 4));
  }
  have viewable(bytes[4 * outer..4 * outer + 4]) by {
   apply(separation::viewable_restrict(memory(bytes[0..8]), memory(bytes[4 * outer..4 * outer + 4])));
  }
  have viewable(chunk[0..4]) by {
   rewrite(chunk, bytes + (4 * outer));
   have contains(memory(bytes[4 * outer..4 * outer + 4]), memory((bytes + (4 * outer))[0..(4 * outer + 4) - (4 * outer)])) by {
    apply(separation::contains_rebase(bytes, 4 * outer, 4 * outer + 4));
   }
   have viewable((bytes + (4 * outer))[0..(4 * outer + 4) - (4 * outer)]) by {
    apply(separation::viewable_restrict(memory(bytes[4 * outer..4 * outer + 4]), memory((bytes + (4 * outer))[0..(4 * outer + 4) - (4 * outer)])));
   }
   have 0 <= 0 by { close(); }
   have 0 <= 4 by { close(); }
   have to_integer(4) <= to_integer((4 * outer + 4) - (4 * outer)) by { close(); }
   have contains(memory((bytes + (4 * outer))[0..(4 * outer + 4) - (4 * outer)]), memory((bytes + (4 * outer))[0..4])) by {
    apply(separation::contains_subrange(bytes + (4 * outer), 0, (4 * outer + 4) - (4 * outer), 0, 4));
   }
   apply(separation::viewable_restrict(memory((bytes + (4 * outer))[0..(4 * outer + 4) - (4 * outer)]), memory((bytes + (4 * outer))[0..4])));
  }
  loop {
   decreases inner;
   views chunk[0..4];
   invariant viewable(chunk[0..4]);
   invariant 0 <= inner and inner <= 1;
   invariant chunk == bytes + (4 * outer);
   invariant 0 <= outer and outer < 2;
   maintain by { step(); step(); step(); step();
    have viewable(chunk[0..4]) by { observe(chunk[0..4]); }
    have (4 * to_integer(outer) <= 2147483647 and 4 * to_integer(outer) >= -2147483648) implies
        chunk == bytes + (4 * outer) implies 0 <= outer and outer < 2 by {
     intro() { intro() { close(); } }
    }
   }
  }
  mark after_inner;
  have 0 <= outer;
  have outer < 2;
  step(); step();
  have to_integer(outer) == to_integer(at(after_inner, outer) + 1);
  have 0 <= at(after_inner, outer);
  have at(after_inner, outer) < 2;
  have 0 <= outer by { close() using { to_integer(outer) == to_integer(at(after_inner, outer) + 1); 0 <= at(after_inner, outer); at(after_inner, outer) < 2; }; }
  have outer <= 2 by { close() using { to_integer(outer) == to_integer(at(after_inner, outer) + 1); 0 <= at(after_inner, outer); at(after_inner, outer) < 2; }; }
  have to_integer(4 * outer) == to_integer(4 * at(after_inner, outer) + 4) by {
   have outer == at(after_inner, outer) + 1;
   rewrite(outer, at(after_inner, outer) + 1);
   if at(after_inner, outer) == 0 {
    rewrite(at(after_inner, outer), 0);
    close();
   } else {
    have at(after_inner, outer) == 1 by {
     normalize() using { 0 <= at(after_inner, outer); at(after_inner, outer) < 2; not (at(after_inner, outer) == 0); };
    }
    rewrite(at(after_inner, outer), 1);
    close();
   }
  }
  have cursor == at(after_inner, cursor) + 4;
  have at(after_inner, cursor) == bytes + (4 * at(after_inner, outer));
  have (bytes + (4 * at(after_inner, outer))) + 4 == bytes + (4 * at(after_inner, outer) + 4) by {
   if at(after_inner, outer) == 0 { close(); } else {
    have at(after_inner, outer) == 1 by { normalize() using { 0 <= at(after_inner, outer); at(after_inner, outer) < 2; not (at(after_inner, outer) == 0); }; }
    rewrite(at(after_inner, outer), 1); close();
   }
  }
  have cursor == bytes + (4 * outer) by { close(); }
  have (4 * to_integer(outer) <= 2147483647 and 4 * to_integer(outer) >= -2147483648) implies
      cursor == bytes + (4 * outer) implies viewable(bytes[0..8]) by {
   intro() { intro() { observe(bytes[0..8]); } }
  }
  have at(after_inner, outer) == at(outer_head, outer);
  have 0 <= 2 - to_integer(outer) by { close() using { outer <= 2; }; }
  have 2 - to_integer(outer) < 2 - to_integer(at(outer_head, outer)) by {
   close() using {
    to_integer(outer) == to_integer(at(after_inner, outer) + 1);
    at(after_inner, outer) == at(outer_head, outer);
    0 <= at(after_inner, outer);
    at(after_inner, outer) < 2;
   };
  }
  have viewable(bytes[0..8]) by { observe(bytes[0..8]); }
 }
 }
}
```

```expect
pass
```
