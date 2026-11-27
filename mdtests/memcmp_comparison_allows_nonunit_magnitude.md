# A comparison relation allows a nonunit magnitude and an arbitrary suffix

A larger first byte permits the positive result seven, regardless of later
bytes. This checks that the relation neither fixes the magnitude nor orders
all differing positions independently.

```click
import click::bytes;
import click::integer;

theorem positive_seven(left: uint8[], right: uint8[]) {
    requires left[0u64] == 2u8;
    requires right[0u64] == 1u8;
    ensures bytes::comparison(left, right, 2u64, 7) by {
        have not bytes::equal(left, 0u64, right, 0u64, 2u64) by {
            if bytes::equal(left, 0u64, right, 0u64, 2u64) {
                unfold(bytes::equal(left, 0u64, right, 0u64, 2u64));
                instantiate((0u64..2u64).all(|k| { left[0u64 + k] == right[0u64 + k] }), 0u64);
                have false by { close(); }
                close();
            } else {
                close();
            }
        }
        have forall (k: uint64) {
            k < 2u64 and bytes::equal_range(left, right, 0u64, k) implies
                (left[k] < right[k] implies 7 < 0) and
                (right[k] < left[k] implies 7 > 0)
        } by {
            intro() {
                intro() {
                    if k == 0u64 {
                        rewrite(k, 0u64);
                        close();
                    } else {
                        have 0u64 <= k by {
                            apply(integer::uint64_to_integer_less_equal_implies_less_equal(0u64, k));
                        }
                        have 0u64 < k by {
                            if 0u64 < k {
                                close();
                            } else {
                                have 0 <= to_integer(k) by { close(); }
                                have to_integer(k) <= 0 by {
                                    close();
                                }
                                have to_integer(k) == 0 by { close(); }
                                have k == 0u64 by { close(); }
                                close();
                            }
                        }
                        unfold(bytes::equal_range(left, right, 0u64, k));
                        instantiate((0u64..k).all(|j| { left[j] == right[j] }), 0u64);
                        close();
                    }
                }
            }
        }
        unfold(bytes::comparison(left, right, 2u64, 7));
        close();
    }
}
```

```expect
pass
```
