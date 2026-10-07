# Unsigned bound weakening preserves the certificate's affine claim

Unsigned comparisons are affine in sign-bit-flipped atoms. A constant slack
weakens a bound without adding wrapping machine operands or treating a
`uint32` value as signed. These bounds include both sides of the sign bit.

```click
theorem lane_ceiling(lane: uint32) {
    requires lane <= 65520u32;
    ensures lane <= 1073741823u32 by {
        arithmetic() using { lane <= 65520u32; }
    }
}

theorem crossing_sign_bit(lane: uint32) {
    requires lane <= 2147483647u32;
    ensures lane <= 2147483648u32 by {
        arithmetic() using { lane <= 2147483647u32; }
    }
}

theorem high_unsigned_ceiling(lane: uint32) {
    requires lane <= 2147483648u32;
    ensures lane <= 4294967294u32 by {
        arithmetic() using { lane <= 2147483648u32; }
    }
}

theorem high_unsigned_floor(lane: uint32) {
    requires 4294967294u32 <= lane;
    ensures 2147483648u32 <= lane by {
        arithmetic() using { 4294967294u32 <= lane; }
    }
}

theorem crossing_sign_bit_floor(lane: uint32) {
    requires 2147483648u32 <= lane;
    ensures 2147483647u32 <= lane by {
        arithmetic() using { 2147483648u32 <= lane; }
    }
}
```

```expect
pass
```
