# Integer casts keep historical values

Integer casts convert the value selected by their operand. Observations at
function entry and at a recorded mark keep their own values after execution.

```c filename=historical_cast.c
int bump(int x) {
    x = x + 1;
    return x;
}
```

```click
verifying "historical_cast.c";
int32 bump(int32 x) {
    requires 0 <= x;
    requires x <= 100;
    ensures to_integer(result) == to_integer(old(x) + 1);
} by {
    mark before;
    step();
    mark after;
    step_until(function.exit);
    have (old(x) as int32) == at(before, x) by close();
    have (at(before, x) as int64) == old(x as int64) by close();
    have at(after, x) == at(before, x) + 1 by { close(); }
    have to_integer(at(after, x)) == to_integer(at(before, x)) + 1 by {
        rewrite(at(after, x), at(before, x) + 1);
        apply(click::integer::int32_add_to_integer(at(before, x), 1));
        close();
    }
    have to_integer(at(after, x)) - to_integer(at(before, x)) == 1 by {
        rewrite(to_integer(at(after, x)), to_integer(at(before, x)) + 1);
        close();
    }
    have ((at(after, x) - at(before, x)) as int32) == 1 by { close(); }
    close();
}
```

```expect
pass
```
