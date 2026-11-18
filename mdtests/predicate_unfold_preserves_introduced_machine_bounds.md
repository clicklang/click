# Predicate unfolding preserves an introduced machine bound

The nested `have` introduces a native index without an enclosing quantified
postcondition reserving its identity. Unfolding the range must keep its end
separate from the new range binder; it must not turn `j < k` into `j < j`.

```click
import click::bytes;

theorem unequal_prefix(left: uint8[], right: uint8[]) {
    requires left[0u64] == 2u8;
    requires right[0u64] == 1u8;
    ensures true by {
        have forall (k: uint64) {
            0u64 < k and bytes::equal_range(left, right, 0u64, k) implies false
        } by {
            intro();
            intro();
            unfold(bytes::equal_range(left, right, 0u64, k));
            instantiate((0u64..k).all(|j| { left[j] == right[j] }), 0u64);
            solve();
        }
        solve();
    }
}
```
```expect
pass
```
