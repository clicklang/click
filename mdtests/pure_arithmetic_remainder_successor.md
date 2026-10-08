# Checked remainder transport through bounded addition

The explicit arithmetic checker transports known residues through a bounded
addition. These lemmas prove the even/odd loop's parity change without changing
the C program. Remainder bounds alone do not establish this relationship.

```click
theorem nonzero_nonnegative(r: int32) {
 requires 0 <= r;
 requires r != 0;
 ensures 1 <= r by { arithmetic() using { 0 <= r; r != 0; } }
}
theorem even_successor(i: int32) {
 requires 0 <= i;
 requires i < 2147483647;
 requires i % 2 == 0;
 ensures (i + 1) % 2 == 1 by {
  have 0 <= i % 2 by { arithmetic() using { i % 2 == 0; } }
  have i % 2 <= 0 by { arithmetic() using { i % 2 == 0; } }
  arithmetic() using { 0 <= i; i < 2147483647; 0 <= i % 2; i % 2 <= 0; }
 }
}
theorem odd_successor(i: int32) {
 requires 0 <= i;
 requires i < 2147483647;
 requires i % 2 != 0;
 ensures (i + 1) % 2 == 0 by {
  have 0 <= i % 2 by { arithmetic() using { 0 <= i; } }
  have i % 2 < 2 by { arithmetic() using { 0 <= i; } }
  have 1 <= i % 2 by apply(nonzero_nonnegative(i % 2));
  have i % 2 <= 1 by { arithmetic() using { 0 <= i; i % 2 < 2; } }
  arithmetic() using { 0 <= i; i < 2147483647; 1 <= i % 2; i % 2 <= 1; }
 }
}

```

```expect
pass
```
