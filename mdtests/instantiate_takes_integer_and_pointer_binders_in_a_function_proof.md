# instantiate takes Integer and pointer binders in a function proof

At a function's outcome, an `Integer` binder takes `to_integer(result)` and a
pointer binder takes `result`. The `requires` universal is matched to the
cited one up to its binder, including through a specification function
applied to an `Integer` binder.

```c filename=instantiate_takes_integer_and_pointer_binders_in_a_function_proof.c
int id(int x) { return x; }
int *keep(int *p) { return p; }
```

```click
verifying "instantiate_takes_integer_and_pointer_binders_in_a_function_proof.c";

function sq(z: Integer) -> Integer { z * z }
function same(p: int32*, q: int32*) -> bool { p == q }

int32 id(int32 x) {
    requires forall (z: Integer) { sq(z) >= 0 };
    ensures sq(to_integer(result)) >= 0;
} by {
    execute();
    have sq(to_integer(result)) >= 0 by {
        instantiate(forall (z: Integer) { sq(z) >= 0 }, to_integer(result));
    }
}

int32* keep(int32* p) {
    requires forall (q: int32*) { same(q, q) };
    ensures same(result, result);
} by {
    execute();
    have same(result, result) by {
        instantiate(forall (q: int32*) { same(q, q) }, result);
    }
}
```

```expect
pass
```
