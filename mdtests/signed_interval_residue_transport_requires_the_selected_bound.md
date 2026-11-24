# Residue transport needs the selected upper bound

The omitted upper bound makes the claim true in the full context, but a
restricted solve must not borrow it to establish the translated residue.

```click
theorem omitted(x: int32) {
    requires 0 <= x;
    requires x <= 100;
    requires 0 <= x % 8;
    requires x % 8 <= 2;
    ensures to_integer(((x + 1) % 8) as int32) <= 3 by {
        close() using { 0 <= x; x <= 100; 0 <= x % 8; };
    }
}
```

```expect
fail: could not prove the current goal from only its listed premises
```
