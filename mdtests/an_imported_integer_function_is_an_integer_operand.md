# An imported Integer function is an Integer operand

Under `arithmetic "integer";` a comparison between an Integer and a machine
value observes the machine side with `to_integer`. A call of a function
declared `-> Integer` is already an Integer, whether the function is declared
in this file or imported: an imported `doubled(x)` is compared as written,
not observed again as `to_integer(doubled(x))`, which does not lower.

```click
arithmetic "integer";

import "an_imported_integer_function_is_an_integer_operand_module.click";

theorem doubled_is_twice(x: int32) {
    ensures to_integer(x) + to_integer(x) == doubled(x) by {
        unfold(doubled(x));
        normalize();
    }
}

theorem doubled_beside_an_observation(x: int32) {
    requires x == 3;
    ensures to_integer(x) * 2 == doubled(x) by {
        have to_integer(x) == 3 by assumption();
        unfold(doubled(x));
        arithmetic() using { to_integer(x) == 3; };
    }
}
```

```expect
pass
```
