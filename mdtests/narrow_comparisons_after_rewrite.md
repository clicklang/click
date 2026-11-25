# Narrow comparisons retain their type after rewriting

```click
theorem int8_comparisons(x: int32) {
    requires x == 9;
    ensures to_integer(x as int8) <= 100 by { rewrite(x, 9); close(); }
    ensures (9 as int8) < (100 as int8) by { close(); }
    ensures not ((100 as int8) <= (9 as int8)) by { close(); }
}

theorem uint8_comparisons(x: int32) {
    requires x == 9;
    ensures to_integer(x as uint8) <= 100 by { rewrite(x, 9); close(); }
    ensures (9 as uint8) < (100 as uint8) by { close(); }
    ensures not ((100 as uint8) <= (9 as uint8)) by { close(); }
}

theorem int16_comparisons(x: int32) {
    requires x == 9;
    ensures to_integer(x as int16) <= 100 by { rewrite(x, 9); close(); }
    ensures (9 as int16) < (100 as int16) by { close(); }
    ensures not ((100 as int16) <= (9 as int16)) by { close(); }
}

theorem uint16_comparisons(x: int32) {
    requires x == 9;
    ensures to_integer(x as uint16) <= 100 by { rewrite(x, 9); close(); }
    ensures (9 as uint16) < (100 as uint16) by { close(); }
    ensures not ((100 as uint16) <= (9 as uint16)) by { close(); }
}

function selected_byte(flag: int32, value: uint64) -> uint8 {
    if flag == 0 { (48u64 + value % 10u64) as uint8 } else { 48 as uint8 }
}

theorem selected_byte_preserves_bound(flag: int32, value: uint64) {
    requires flag == 0;
    ensures (48 as uint8) <= selected_byte(flag, value) by {
        unfold(selected_byte(flag, value));
        have (48 as uint8) <= (48u64 + value % 10u64) as uint8 by {
            normalize() using {};
        }
        rewrite(flag, 0); close();
        close();
    }
}

```

```expect
pass
```
