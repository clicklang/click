# A call is named among the function's calls

`call(f, j)` on its own names the function's `j`th call of `f`, counting its
calls in the order they run, and `call(j)` its `j`th call of any function.
Here `twice` is called twice, in two statements: `call(twice, 1)` is the
second, in `statement(1)`, the same call `statement(1).call(twice, 0)` names.

```c filename=function_calls.c
int32 twice(int32 x);
int32 f(int32 a) {
    int32 b = twice(a) + 1;
    int32 c = twice(b) + 1;
    return c;
}
```

```click
import click::integer;
extern int32 twice(int32 x) {
    requires defined(x + x);
    ensures result == x + x;
}
verifying "function_calls.c";
int32 f(int32 a) {
    requires a >= 0 and a <= 100;
    ensures result == 4 * a + 3;
} by {
    step_until(statement(0).call(twice, 0).entry);
    let { result: first } = step();
    step();
    have call(twice, 0).result == a + a;
    have to_integer(b) == to_integer(first) + 1 by {
        apply(integer::int32_add_to_integer(first, 1));
        close();
    }

    // The first call doubles a value in [0, 100], so b is in [1, 201].
    have 0 <= to_integer(a) by close() using { a >= 0; };
    have to_integer(a) <= 100 by close() using { a <= 100; };
    apply(integer::add_le(0, to_integer(a), 0, to_integer(a)));
    apply(integer::add_le(to_integer(a), 100, to_integer(a), 100));
    have to_integer(first) == to_integer(a) + to_integer(a) by close();
    have 0 <= to_integer(first) by {
        rewrite(to_integer(first), to_integer(a) + to_integer(a));
        close();
    }
    have to_integer(first) <= 200 by {
        rewrite(to_integer(first), to_integer(a) + to_integer(a));
        close();
    }
    apply(integer::add_le(0, to_integer(first), 1, 1));
    apply(integer::add_le(to_integer(first), 200, 1, 1));
    have 1 <= to_integer(b) by {
        rewrite(to_integer(b), to_integer(first) + 1);
        close();
    }
    have to_integer(b) <= 201 by {
        rewrite(to_integer(b), to_integer(first) + 1);
        close();
    }

    // The second call doubles b within the signed int32 range.
    apply(integer::add_le(1, to_integer(b), 1, to_integer(b)));
    apply(integer::add_le(to_integer(b), 201, to_integer(b), 201));
    have -2147483648 <= to_integer(b) + to_integer(b) by {
        apply(integer::le_transitive(-2147483648, 2, to_integer(b) + to_integer(b)));
    }
    have to_integer(b) + to_integer(b) <= 2147483647 by {
        apply(integer::le_transitive(to_integer(b) + to_integer(b), 402, 2147483647));
    }
    step_until(statement(1).call(twice, 0).entry);
    step() by { close(); }

    step();

    have call(twice, 1).result == statement(1).call(twice, 0).result;
    have call(1).result == call(twice, 1).result;
    have to_integer(c) == to_integer(call(twice, 1).result) + 1 by {
        apply(integer::int32_add_to_integer(call(twice, 1).result, 1));
        close();
    }
    have to_integer(call(twice, 1).result) == to_integer(b) + to_integer(b);
    have to_integer(c) == 4 * to_integer(a) + 3 by {
        rewrite(to_integer(c), to_integer(call(twice, 1).result) + 1);
        rewrite(to_integer(call(twice, 1).result), to_integer(b) + to_integer(b));
        rewrite(to_integer(b), to_integer(first) + 1);
        rewrite(to_integer(first), to_integer(a) + to_integer(a));
        close();
    }
    step();
    have to_integer(result) == to_integer(4 * a + 3) by {
        have to_integer(4 * a + 3) == 4 * to_integer(a) + 3;
        rewrite(to_integer(4 * a + 3), 4 * to_integer(a) + 3);
        close();
    }
    close();
}
```

```expect
pass
```
