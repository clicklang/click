# Function parameters in specification functions

Callbacks have explicit, fixed signatures. Named functions may call, alias,
and forward them. At a concrete call the callback is a lambda value; memory
reads retain their application state and ordinary validity obligations.

```c filename=callbacks.c
void write(int32* p) { p[0] = 5; }
```

```click
import "specification_function_parameters_model.click";

verifying "callbacks.c";

function twice(f: fn(Integer) -> Integer, x: Integer) -> Integer {
    f(f(x))
}

function forward(f: fn(Integer) -> Integer, x: Integer) -> Integer {
    let alias: fn(Integer) -> Integer = f;
    twice(alias, x)
}

function captured(offset: Integer) -> Integer {
    let add = |x: Integer| -> Integer { x + offset };
    let offset: Integer = 100;
    forward(add, 3)
}

function reduce(step: fn(Integer, int32) -> Integer, lo: int32, hi: int32, initial: Integer) -> Integer {
    (lo..hi).fold(initial, step)
}

function every(predicate: fn(int32) -> Prop, lo: int32, hi: int32) -> Prop {
    (lo..hi).all(predicate)
}

function some(predicate: fn(int32) -> Prop, lo: int32, hi: int32) -> Prop {
    (lo..hi).any(predicate)
}

function access(read: fn(int32) -> Integer, i: int32) -> Integer { read(i) }

spec enum Boxed { Value(Integer) }
function wrap(f: fn(Integer) -> Integer, x: Integer) -> Boxed { Boxed::Value(f(x)) }
function accepts(p: fn(Integer) -> Prop, b: Boxed) -> Prop { b == Boxed::Value(4) and p(4) }
theorem algebraic_callbacks() {
    ensures wrap(|x: Integer| -> Integer { x + 1 }, 3) == Boxed::Value(4) by {
        unfold(wrap(|x: Integer| -> Integer { x + 1 }, 3)); have to_integer(3) + 1 == 4 by solve(); solve();
    }
    ensures accepts(|x: Integer| -> Prop { x == 4 }, Boxed::Value(4)) by solve();
}

theorem imported_callbacks(lo: int32, hi: int32) {
    ensures imported_twice(|x: Integer| -> Integer { x + 1 }, 3) == 5 by {
        unfold(imported_twice(|x: Integer| -> Integer { x + 1 }, 3)); solve();
    }
    ensures imported_every(|i: int32| -> Prop { i < hi }, lo, hi) by {
        intro(); intro(); solve();
    }
}

theorem application() {
    let increment = |x: Integer| -> Integer { x + 1 };
    ensures twice(increment, 3) == 5 by {
        unfold(twice(increment, 3));
        solve();
    }
    ensures captured(5) == 13 by { unfold(captured(5)); solve(); }
}

theorem range_callbacks(lo: int32, hi: int32, offset: Integer) {
    let step = |acc: Integer, i: int32| -> Integer { acc + to_integer(i) + offset };
    let predicate = |i: int32| -> Prop { i < hi };
    ensures reduce(step, lo, hi, 0) == (lo..hi).fold(0, step) by {
        unfold(reduce(step, lo, hi, 0)); solve();
    }
    ensures every(predicate, lo, hi) by { intro(); intro(); solve(); }
}

theorem callback_fold_append(lo: int32, hi: int32) {
    requires lo <= hi;
    requires hi < 2147483647;
    ensures reduce(|acc: Integer, i: int32| -> Integer { acc + to_integer(i) }, lo, hi + 1, 0) == reduce(|acc: Integer, i: int32| -> Integer { acc + to_integer(i) }, lo, hi, 0) + to_integer(hi) by {
        peel(reduce(|acc: Integer, i: int32| -> Integer { acc + to_integer(i) }, lo, hi + 1, 0)) using { lo <= hi; hi < 2147483647; };
        solve();
    }
}

function math_total(step: fn(Integer, Integer) -> Integer, lo: Integer, hi: Integer) -> Integer {
    (lo..hi).fold(0, step)
}
theorem mathematical_callback_fold_append(lo: Integer, hi: Integer) {
    requires lo <= hi;
    ensures math_total(|acc: Integer, i: Integer| -> Integer { acc + i }, lo, hi + 1) == math_total(|acc: Integer, i: Integer| -> Integer { acc + i }, lo, hi) + hi by {
        have hi + 1 - 1 == hi by solve();
        have lo <= hi + 1 - 1 by solve();
        peel(math_total(|acc: Integer, i: Integer| -> Integer { acc + i }, lo, hi + 1)) using { lo <= hi + 1 - 1; };
        solve();
    }
}

theorem existential_callback(lo: int32, hi: int32) {
    requires lo < hi;
    ensures some(|i: int32| -> Prop { i == lo }, lo, hi) by { witness { item: lo }; solve(); }
}

void write(int32* p) {
    owns p[0..1];
    requires p[0] == 0;
    ensures access(|i: int32| -> Integer { to_integer(p[i]) }, 0) == 5 by {
        step_until(function.exit);
        unfold(access(|i: int32| -> Integer { to_integer(p[i]) }, 0));
        solve();
    }
}
```

```expect
pass
```
