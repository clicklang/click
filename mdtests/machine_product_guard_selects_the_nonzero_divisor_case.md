# Resolve an explicit disjunction
```click
theorem bridge(left: uint32, right: uint32) {
    requires right == 0u32 or left <= 4294967295u32 / right;
    requires right != 0u32;
    ensures to_integer(left) <= to_integer(4294967295u32 / right) by {
        cases {
            right == 0u32 => { contradiction(right == 0u32); }
            to_integer(left) <= to_integer(4294967295u32 / right) => { close(); }
        }
    }
}
```
```expect
pass
```
