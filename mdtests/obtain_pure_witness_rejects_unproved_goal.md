# Resolving a witness does not prove an unrelated bound

The scope error's original report used a conclusion that does not follow
from its premises. Fixing name resolution must leave that goal open.

```click
theorem original_goal(x: int32) {
    requires exists (k: int32) { k > x };
    requires forall (j: int32) { j > x implies j > 1000 };
    ensures x < 1000 by {
        obtain (k: int32) { k > x }
        instantiate(forall (j: int32) { j > x implies j > 1000 }, k)
            using { k > x; }
        simp();
    }
}
```

```expect
fail: could not establish `x < 1000`
```
