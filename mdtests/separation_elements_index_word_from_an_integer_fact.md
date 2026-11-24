# `separation::separate_elements` takes its index word fact from an Integer fact

`separation::separate_elements(q, m - 1, 0)` requires `i != j` of the `int32` index
words: `((m - 1) as int32) != 0`. The contract states the Integer fact
`m - 1 != 0`, which `apply ... using { m - 1 != 0; }` refuses as a
different fact. `solve` proves the word fact from it, by cases on the word
equality, because `defined(m - 1)` keeps the word equal to the Integer. The
explicit preservation below then carries `q[0]` across the store.

```c filename=separation_elements_index_word_from_an_integer_fact.c
int read_first(int m) {
    int *q = malloc(m * sizeof(int));
    if (q == 0) {
        return 0;
    }
    q[0] = 7;
    q[m - 1] = 1;
    int r = q[0];
    free(q);
    return r;
}
```

```click
import click::separation;
verifying "separation_elements_index_word_from_an_integer_fact.c";

int32 read_first(int32 m) {
    requires 1 <= m;
    requires m <= 1000;
    requires m - 1 != 0;
    ensures result == 0 or result == 7;
} by {
    step(); step();
    if q == 0 {
    } else {
        step_until(statement(3).entry);
        have q[0] == 7 by close();
        mark before_store;
        step();
        have defined(m - 1) by close();
        have ((m - 1) as int32) != 0 by close();
        have separate(memory(q[m - 1]), memory(q[0])) by {
            apply(separation::separate_elements(q, m - 1, 0));
        }
        have separate(statement(3).footprint, memory(q[0])) by {
            close() using { separate(memory(q[m - 1]), memory(q[0])); };
        }
        have q[0] == at(before_store, q[0]) by {
            preserve(memory(q[0]), statement(3));
        }
        have q[0] == 7 by close();
        step_until(function.exit);
    }
}
```

```expect
pass
```
