# Mathematical product bounds establish the original checked multiplication guard

```click
import click::integer;

theorem product_bound_guard(left: uint32, right: uint32) {
    requires to_integer(left) * to_integer(right) <= 4294967295;
    ensures right == 0u32 or left <= 4294967295u32 / right by {
        apply(integer::uint32_multiply_guard_by_integer_bound(left, right)) using {
            to_integer(left) * to_integer(right) <= 4294967295;
        };
    }
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by {
        apply(integer::uint32_multiply_guard_by_integer_bound(left, right)) using {
            to_integer(left) * to_integer(right) <= 4294967295;
        };
        apply(integer::uint32_multiply_to_integer(left, right)) using {
            right == 0u32 or left <= 4294967295u32 / right;
        };
    }
}

theorem zero_product_guard(left: uint32) {
    ensures 0u32 == 0u32 or left <= 4294967295u32 / 0u32 by auto();
}
```

```expect
pass
```
