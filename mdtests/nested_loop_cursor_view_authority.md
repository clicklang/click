# Nested loops retain input authority through proved cursor aliases

The inner loop calls a checked reader through the abstract outer cursor.
A checked pointer equality and input subrange carry its byte view and stable
loan binding into the nested loop. The input bytes are unchanged.

```c filename=alias-nested-call.c
int32 read(const uint8* p) { return p[0]; }
int32 f(const uint8* bytes) { const uint8* cursor = bytes; int32 outer = 0; while (outer < 2) { const uint8* chunk = cursor; int32 inner = 1; while (inner > 0) { int32 value = read(chunk); inner -= 1; } cursor += 4; outer += 1; } return 0; }
```

```click
verifying "alias-nested-call.c";
int32 read(const uint8* p) { views p[0..4]; ensures 0 <= result and result <= 255; } by { execute(); simp(); }
int32 f(const uint8* bytes) { views bytes[0..8]; ensures result == 0; } by {
 execute_until(loop(0));
 have viewable(bytes[0..8]) by { transport(at(function.entry,viewable(bytes[0..8])),viewable(bytes[0..8])) using { at(function.entry,viewable(bytes[0..8])); 0 <= 8; } }
 loop {
 decreases 2 - outer;
 views bytes[0..8];
 invariant 0 <= outer and outer <= 2;
 invariant cursor == bytes + (4 * outer);
 invariant bytes == old(bytes);
 invariant viewable(bytes[0..8]);
 preserve by {
  have outer < 2;
  mark outer_head;
  execute_until(loop(1));
  have chunk == bytes + (4 * outer);
  have 0 <= 4 * outer by { arithmetic() using { 0 <= outer; outer < 2; } }
  have 4 * outer <= 4 by { arithmetic() using { 0 <= outer; outer < 2; } }
  have 4 * outer + 4 <= 8 by { arithmetic() using { 0 <= outer; outer < 2; } }
  have 4 * outer <= 4 * outer + 4 by { arithmetic() using { 0 <= outer; outer < 2; } }
  have viewable(bytes[0..8]) by { transport(at(outer_head,viewable(bytes[0..8])),viewable(bytes[0..8])) using { at(outer_head,viewable(bytes[0..8])); bytes == old(bytes); 0 <= 8; } }
  have viewable(bytes[4 * outer..4 * outer + 4]) by { transport(viewable(bytes[0..8]),viewable(bytes[4 * outer..4 * outer + 4])) using { viewable(bytes[0..8]); 0 <= 4 * outer; 4 * outer <= 4 * outer + 4; 4 * outer + 4 <= 8; } }
  have viewable(chunk[0..4]) by { rewrite(chunk == bytes + (4 * outer)); simp() using { viewable(bytes[4 * outer..4 * outer + 4]); } }
  loop {
   decreases inner;
   views chunk[0..4];
   invariant viewable(chunk[0..4]);
   invariant 0 <= inner and inner <= 1;
   invariant chunk == bytes + (4 * outer);
   invariant 0 <= outer and outer < 2;
   preserve by { mark inner_head; step(); step(); step();
    have viewable(chunk[0..4]) by { transport(at(inner_head,viewable(chunk[0..4])),viewable(chunk[0..4])) using { at(inner_head,viewable(chunk[0..4])); 0 <= 4; } }
    close_invariants by { simp(); }
   }
  }
  mark after_inner;
  have 0 <= outer;
  have outer < 2;
  step(); step();
  have outer == at(after_inner, outer) + 1;
  have 0 <= at(after_inner, outer);
  have at(after_inner, outer) < 2;
  have 0 <= outer by { arithmetic() using { outer == at(after_inner, outer) + 1; 0 <= at(after_inner, outer); at(after_inner, outer) < 2; } }
  have outer <= 2 by { arithmetic() using { outer == at(after_inner, outer) + 1; 0 <= at(after_inner, outer); at(after_inner, outer) < 2; } }
  have 4 * outer == 4 * at(after_inner, outer) + 4 by { arithmetic() using { outer == at(after_inner, outer) + 1; 0 <= at(after_inner, outer); at(after_inner, outer) < 2; } }
  have cursor == at(after_inner, cursor) + 4;
  have at(after_inner, cursor) == bytes + (4 * at(after_inner, outer));
  have (bytes + (4 * at(after_inner, outer))) + 4 == bytes + (4 * at(after_inner, outer) + 4) by {
   if at(after_inner, outer) == 0 { simp(); } else {
    have at(after_inner, outer) == 1 by { arithmetic() using { 0 <= at(after_inner, outer); at(after_inner, outer) < 2; not (at(after_inner, outer) == 0); } }
    rewrite(at(after_inner, outer) == 1); simp();
   }
  }
  have cursor == bytes + (4 * outer) by {
   rewrite(cursor == at(after_inner, cursor) + 4);
   rewrite(at(after_inner, cursor) == bytes + (4 * at(after_inner, outer)));
   rewrite((bytes + (4 * at(after_inner, outer))) + 4 == bytes + (4 * at(after_inner, outer) + 4));
   rewrite(4 * at(after_inner, outer) + 4 == 4 * outer);
   normalize();
  }
  have viewable(bytes[0..8]) by { transport(at(outer_head,viewable(bytes[0..8])),viewable(bytes[0..8])) using { at(outer_head,viewable(bytes[0..8])); bytes == old(bytes); 0 <= 8; } }
  close_invariants by { simp(); }
 }
 }
 execute(); simp();
}
```

```expect
pass
```
