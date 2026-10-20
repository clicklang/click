# A rewrite written over an observation rewrites its Integer

`to_integer(x) == 1` is stated as the native comparison `x == 1u32`. A
`rewrite` by it still rewrites the Integer `1` the goal names, through its
Integer reading, as it is written. A machine `1u64` elsewhere in the goal is
not a reading of that equality and stays as it is.

```click
import click::integer;

function twice(n: Integer) -> Integer { n + n }

theorem rewrite_by_an_observation(x: uint32, y: uint64) {
    requires to_integer(x) == 1;
    ensures twice(to_integer(x)) + to_integer(y % 1u64) == twice(1) + to_integer(y % 1u64) by {
        rewrite(1 == to_integer(x));
        normalize();
    }
}
```

```expect
pass
```
