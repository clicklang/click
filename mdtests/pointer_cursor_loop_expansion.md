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
theorem nonzero_binary_index(value: int32) {
    requires 0 <= value;
    requires value < 2;
    requires value != 0;
    ensures value == 1 by {
        apply(click::integer::int32_less_equal_and_not_equal_implies_less_than(0, value));
        have 1 <= to_integer(value) by {
            apply(click::integer::lt_step_le(0, to_integer(value)));
            close();
        }
        have to_integer(value) <= 1 by {
            apply(click::integer::lt_le_predecessor(to_integer(value), 2));
            close();
        }
        apply(click::integer::le_antisymmetric(to_integer(value), 1));
        close();
    }
}

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
  have to_integer(4 * outer) == to_integer(4 * at(after_inner, outer) + 4) by {
   have outer == at(after_inner, outer) + 1;
   rewrite(outer, at(after_inner, outer) + 1);
   if at(after_inner, outer) == 0 {
    rewrite(at(after_inner, outer), 0);
    close();
   } else {
    have at(after_inner, outer) == 1 by {
     apply(nonzero_binary_index(at(after_inner, outer)));
    }
    rewrite(at(after_inner, outer), 1);
    close();
   }
  }
  have cursor == at(after_inner, cursor) + 4;
  have at(after_inner, cursor) == bytes + (4 * at(after_inner, outer));
  have (bytes + (4 * at(after_inner, outer))) + 4 == bytes + (4 * at(after_inner, outer) + 4) by {
   if at(after_inner, outer) == 0 { close(); } else {
    have at(after_inner, outer) == 1 by { apply(nonzero_binary_index(at(after_inner, outer))); }
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
