# Checked unsigned products retain their exact mathematical value

```click
theorem checked_product(a: uint32, b: uint32) {
    requires b == 0u32 or a <= 4294967295u32 / b;
    ensures to_integer(a * b) == to_integer(a) * to_integer(b) by {
        apply(uint32_mul_to_integer(a, b));
    }
}

theorem zero_factor(a: uint32) {
    ensures to_integer(a * 0u32) == 0 by {
        apply(uint32_mul_to_integer(a, 0u32));
        simp();
    }
}

theorem known_zero_factor(a: uint32, b: uint32) {
    requires b == 0u32;
    ensures to_integer(a * b) == 0 by {
        apply(uint32_mul_to_integer(a, b));
        rewrite(to_integer(a * b) == to_integer(a) * to_integer(b));
        have to_integer(b) == 0;
        rewrite(to_integer(b) == 0);
        arithmetic() using {};
    }
}

theorem full_unsigned_range() {
    ensures to_integer(4294967295u32 * 1u32) == 4294967295 by {
        apply(uint32_mul_to_integer(4294967295u32, 1u32));
        simp();
    }
}

theorem reduced_lane_ceiling(lane: uint32) {
    requires lane <= 65520u32;
    ensures to_integer(lane * 4u32) <= 262080 by {
        have lane <= 4294967295u32 / 4u32 by {
            arithmetic() using { lane <= 65520u32; }
        }
        have 4u32 == 0u32 or lane <= 4294967295u32 / 4u32 by {
            assumption();
        }
        apply(uint32_mul_to_integer(lane, 4u32));
        apply(uint32_less_equal_to_integer(lane, 65520u32));
        arithmetic() using {
            to_integer(lane * 4u32) == to_integer(lane) * 4;
            to_integer(lane) <= 65520;
        }
    }
}
```

```expect
pass
```
