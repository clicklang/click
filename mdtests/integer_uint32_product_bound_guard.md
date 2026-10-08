# Mathematical product bounds establish the original checked multiplication guard

```click
theorem product_bound_guard(left: uint32, right: uint32) {
    requires to_integer(left) * to_integer(right) <= 4294967295;
    ensures right == 0u32 or left <= 4294967295u32 / right by {
        apply(uint32_mul_guard_by_integer_bound(left, right)) using {
            to_integer(left) * to_integer(right) <= 4294967295;
        }
    }
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by {
        apply(uint32_mul_guard_by_integer_bound(left, right)) using {
            to_integer(left) * to_integer(right) <= 4294967295;
        }
        apply(uint32_mul_to_integer(left, right)) using {
            right == 0u32 or left <= 4294967295u32 / right;
        }
    }
}

theorem zero_product_guard(left: uint32) {
    ensures 0u32 == 0u32 or left <= 4294967295u32 / 0u32 by {
        have to_integer(left) * to_integer(0u32) <= 4294967295 by { arithmetic() using {}; }
        apply(uint32_mul_guard_by_integer_bound(left, 0u32)) using {
            to_integer(left) * to_integer(0u32) <= 4294967295;
        }
    }
}
```

```expect
pass
```
