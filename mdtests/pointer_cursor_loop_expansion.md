# A pointer loop invariant keeps its pointer type in expansion

The symbolic offset contains an `int32` multiplication, but the complete
`bytes + (4 * outer)` expression is a pointer. Expanding the loop invariant
must not cast that entire expression to `int32`.

```c filename=cursor-loop.c
int32 f(const uint8* bytes) {
    const uint8* cursor = bytes;
    int32 outer = 0;
    while (outer < 2) { cursor += 4; outer += 1; }
    return 0;
}
```

```click
verifying "cursor-loop.c";
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
  mark after_inner;
  have 0 <= outer;
  have outer < 2;
  step(); step();
  have to_integer(outer) == to_integer(at(after_inner, outer) + 1);
  have 0 <= at(after_inner, outer);
  have at(after_inner, outer) < 2;
  have 0 <= outer by { close() using { to_integer(outer) == to_integer(at(after_inner, outer) + 1); 0 <= at(after_inner, outer); at(after_inner, outer) < 2; }; }
  have outer <= 2 by { close() using { to_integer(outer) == to_integer(at(after_inner, outer) + 1); 0 <= at(after_inner, outer); at(after_inner, outer) < 2; }; }
  have to_integer(4 * outer) == to_integer(4 * at(after_inner, outer) + 4) by { close() using { to_integer(outer) == to_integer(at(after_inner, outer) + 1); 0 <= at(after_inner, outer); at(after_inner, outer) < 2; }; }
  have cursor == at(after_inner, cursor) + 4;
  have at(after_inner, cursor) == bytes + (4 * at(after_inner, outer));
  have (bytes + (4 * at(after_inner, outer))) + 4 == bytes + (4 * at(after_inner, outer) + 4) by {
   if at(after_inner, outer) == 0 { close(); } else {
    have at(after_inner, outer) == 1 by { close() using { 0 <= at(after_inner, outer); at(after_inner, outer) < 2; not (at(after_inner, outer) == 0); }; }
    rewrite(at(after_inner, outer), 1); close();
   }
  }
  have cursor == bytes + (4 * outer) by { close(); }
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
