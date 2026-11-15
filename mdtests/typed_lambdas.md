# Typed lambdas and explicit application

Specification lambdas are lexical values with typed parameters and results.
Applications preserve captures across shadowing and bind arguments
simultaneously. They do not require higher-order proof search.

```click
function captured(offset: Integer) -> Integer {
    let add = |x: Integer| -> Integer { x + offset };
    let offset: Integer = 100;
    add(2)
}

function shadowed_argument(offset: Integer) -> Integer {
    let add = |x: Integer| -> Integer { x + offset };
    let offset: Integer = 100;
    add(offset)
}

function composed(value: Integer) -> Integer {
    let inc = |x: Integer| -> Integer { x + 1 };
    let twice = |x: Integer| -> Integer { inc(inc(x)) };
    let alias: fn(Integer) -> Integer = twice;
    alias(value)
}

function plus_one(value: Integer) -> Integer {
    value + 1
}

theorem lambda_application() {
    ensures (|| -> Integer { 7 })() == 7 by solve();
    ensures (|x: Bool| -> Bool { x })(true) == true by solve();
    ensures (|x: uint8| -> uint8 { x + 1 })(255u8) == 0u8 by solve();
    ensures (|x: Integer| -> Integer { x + 1 })(3) == 4 by solve();
    ensures (|x: int32| -> int32 { x })(7) == 7 by solve();
    ensures (|x: uint64| -> uint64 { x })(7u64) == 7u64 by solve();
}

theorem lambda_capture() {
    ensures shadowed_argument(5) == 105 by {
        unfold(shadowed_argument(5));
        solve();
    }
    ensures captured(5) == 7 by {
        unfold(captured(5));
        solve();
    }
    ensures composed(5) == 7 by {
        unfold(composed(5));
        solve();
    }
}

theorem simultaneous_arguments(x: Integer, y: Integer) {
    ensures (|x: Integer, y: Integer| -> Integer { x - y })(y, x) == y - x by solve();
}

theorem lambda_machine_arithmetic(value: int32) {
    ensures (|x: int32| -> Integer { x + 1 })(value) == to_integer(value) + 1 by solve();
    ensures (|x: Integer| -> Integer { plus_one(x) })(5) == 6 by {
        unfold(plus_one(5));
        solve();
    }
}

```

```expect
pass
```
