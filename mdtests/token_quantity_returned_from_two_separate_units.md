# Two units of one token returned from two separate holdings

`pipeline` returns `2 of slot(pool)`. `initialize` produces both slots as one
held unit; `checkout(first)` takes one of them, and `give_back(first)`
produces a slot again. At the return the body holds `slot(pool) x 1` twice:
the remainder of the first unit and the unit `give_back` produced. Neither
covers the returned quantity alone, and the return check consumes without
normalizing first, so it must take the quantity from both units together.
It merges same-resource units it already selected, and keeps a unit with a
borrow, support, projection or witness apart.

```c filename=pool.c
struct pool { int32 checked_out; int32 capacity; };
struct payload { int32 value; };
void initialize(struct pool* pool, int32 amount) { pool->checked_out=0; pool->capacity=amount; }
void checkout(struct pool* pool, struct payload* p) { pool->checked_out=pool->checked_out+1; }
void give_back(struct pool* pool, struct payload* p) { pool->checked_out=pool->checked_out-1; }
void pipeline(struct pool* pool, struct payload* first, struct payload* second) {
 initialize(pool,2); checkout(pool,first); give_back(pool,first);
}
```

```click
import click::integer;

authorized resource slot(pool: struct pool*) {}
authorized resource item(pool: struct pool*, p: struct payload*) { owns *p; }
resource storage(pool: struct pool*) {
    owns *pool;
    owns authority(slot(pool));
    owns authority(item(pool, _));
}
resource control(pool: struct pool*) {
    owns *pool;
    owns authority(slot(pool));
    owns authority(item(pool, _));
    fact 0 <= pool->checked_out;
    fact pool->checked_out == count(item(pool, _));
    fact pool->capacity == pool->checked_out + count(slot(pool));
}
verifying "pool.c";
void initialize(struct pool* pool, int32 amount) {
    consumes storage(pool);
    requires 0 <= amount;
    requires count(slot(pool)) == 0;
    requires count(item(pool, _)) == 0;
    produces control(pool);
    produces amount of slot(pool);
    ensures pool->capacity == amount;
    ensures pool->checked_out == 0;
    ensures count(item(pool, _)) == 0;
} by {
    unfold(storage(pool));
    step();
    step();
    fold(amount of slot(pool));
    fold(control(pool));
    step();
}
void checkout(struct pool* pool, struct payload* p) {
    owns control(pool);
    requires pool->checked_out < 2147483647;
    consumes slot(pool);
    consumes *p;
    produces item(pool, p);
    ensures count(slot(pool)) == old(count(slot(pool))) - 1;
    ensures count(item(pool, _)) == old(count(item(pool, _))) + 1;
    ensures pool->checked_out == old(pool->checked_out) + 1;
    ensures pool->capacity == old(pool->capacity);
} by {
    with(control(pool)) {
        have 1 <= to_integer(count(slot(pool))) by {
            close();
        }
        have defined((pool->checked_out + 1)) by {
            close() using { at(function.entry, pool->checked_out) < at(function.entry, 2147483647); };
        }
        apply(integer::int32_add_to_integer(pool->checked_out, 1));
        unfold(slot(pool));
        step();
        fold(item(pool, p));
        have to_integer(pool->capacity) == (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) by {
            have -2147483648 <= (to_integer(old(pool->checked_out)) + 1) by {
                close() using { 0 <= to_integer(old(pool->checked_out)); };
            }
            have (to_integer(old(pool->checked_out)) + 1) <= 2147483647 by {
                close() using { to_integer(old(pool->checked_out)) < 2147483647; };
            }
            have to_integer(pool->checked_out) == (to_integer(old(pool->checked_out)) + 1) by {
                have pool->checked_out == old(pool->checked_out) + 1;
                rewrite(pool->checked_out, old(pool->checked_out) + 1);
                close();
            }
            have -2147483648 <= (to_integer(old(count(slot(pool)))) - 1) by {
                close() using { 1 <= to_integer(old(count(slot(pool)))); };
            }
            have (to_integer(old(count(slot(pool)))) - 1) <= 2147483647 by {
                close() using {  };
            }
            have to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool)))) - 1) by {
                close() using { -2147483648 <= (to_integer(old(count(slot(pool)))) - 1); (to_integer(old(count(slot(pool)))) - 1) <= 2147483647; };
            }
            have to_integer(pool->capacity) <= (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) by {
                close() using { at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool))))); to_integer(pool->checked_out) == (to_integer(old(pool->checked_out))
                        + 1); to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool))))
                        - 1); };
            }
            have (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) <= to_integer(pool->capacity) by {
                close() using { at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool))))); to_integer(pool->checked_out) == (to_integer(old(pool->checked_out))
                        + 1); to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool))))
                        - 1); };
            }
            close() using { to_integer(pool->capacity) <= (to_integer(pool->checked_out) +
                    to_integer(count(slot(pool)))); (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) <=
                    to_integer(pool->capacity); };
        }
    }
    step();
    close();
    have to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool)))) - 1) by {
        have -2147483648 <= (to_integer(old(count(slot(pool)))) - 1) by {
            close() using { 1 <= to_integer(old(count(slot(pool)))); };
        }
        have (to_integer(old(count(slot(pool)))) - 1) <= 2147483647 by {
            close() using {  };
        }
        have to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool)))) - 1) by {
            close() using { -2147483648 <= (to_integer(old(count(slot(pool)))) - 1); (to_integer(old(count(slot(pool)))) - 1) <= 2147483647; };
        }
        close();
    }
    have to_integer(count(item(pool, _))) == (to_integer(old(count(item(pool, _)))) + 1) by {
        have to_integer(count(item(pool, _))) <= (to_integer(old(count(item(pool, _)))) + 1) by {
            close() using { at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool))))); at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer((pool->checked_out + 1)) + to_integer((old(count(slot(pool))) -
                    1)))); to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool)))) - 1); to_integer(old(pool->checked_out)) == to_integer(old(count(item(pool,
                    _)))); to_integer(pool->checked_out) == to_integer(count(item(pool, _))); to_integer(pool->checked_out) == to_integer(old(pool->checked_out) + 1); };
        }
        have (to_integer(old(count(item(pool, _)))) + 1) <= to_integer(count(item(pool, _))) by {
            close() using { at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool))))); at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer((pool->checked_out + 1)) + to_integer((old(count(slot(pool))) -
                    1)))); to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool)))) - 1); to_integer(old(pool->checked_out)) == to_integer(old(count(item(pool,
                    _)))); to_integer(pool->checked_out) == to_integer(count(item(pool, _))); to_integer(pool->checked_out) == to_integer(old(pool->checked_out) + 1); };
        }
        close() using { to_integer(count(item(pool, _))) <= (to_integer(old(count(item(pool, _)))) +
                1); (to_integer(old(count(item(pool, _)))) + 1) <= to_integer(count(item(pool,
                _))); };
    }
    have to_integer(pool->checked_out) == (to_integer(old(pool->checked_out)) + 1) by {
        close();
    }
    close();
    close();
    close();
    close();
    close();
}
void give_back(struct pool* pool, struct payload* p) {
    owns control(pool);
    requires count(item(pool, p)) == 1;
    consumes item(pool, p);
    produces *p;
    produces slot(pool);
    ensures count(slot(pool)) == old(count(slot(pool))) + 1;
    ensures count(item(pool, _)) == old(count(item(pool, _))) - 1;
    ensures pool->checked_out == old(pool->checked_out) - 1;
    ensures pool->capacity == old(pool->capacity);
    ensures defined(pool->checked_out + count(slot(pool)));
    ensures pool->capacity == pool->checked_out + count(slot(pool));
    ensures p->value == old(p->value);
} by {
    with(control(pool)) {
        have 1 <= to_integer(count(item(pool, _))) by {
            close();
        }
        have 1 <= pool->checked_out by {
            rewrite(to_integer(pool->checked_out), to_integer(count(item(pool, _))));
            close();
        }
        have defined((count(slot(pool)) + 1)) by {
            have (to_integer(count(slot(pool))) + to_integer(1)) >= -2147483648 by {
                close() using { 0 <= to_integer(count(slot(pool))); };
            }
            have (to_integer(count(slot(pool))) + to_integer(1)) <= 2147483647 by {
                close() using { at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool))))); 1 <= to_integer(pool->checked_out); };
            }
            close();
        }
        unfold(item(pool, p));
        have separate(memory(p->value), memory(pool->checked_out));
        apply(integer::int32_subtract_to_integer(pool->checked_out, 1));
        step();
        have separate(statement(0).footprint, memory(p->value)) by {
            close() using { separate(memory(p->value), memory(pool->checked_out)); };
        }
        have p->value == old(p->value) by {
            preserve(memory(p->value), statement(0));
        }
        fold(slot(pool));
        have 0 <= pool->checked_out by {
            close() using { at(function.entry, 1) <= at(function.entry, pool->checked_out); };
        }
        have to_integer(pool->checked_out) == to_integer(count(item(pool, _))) by {
            close();
        }
        have to_integer(pool->capacity) == (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) by {
            have -2147483648 <= (to_integer(old(pool->checked_out)) - 1) by {
                close() using { 0 <= to_integer(old(pool->checked_out)); };
            }
            have (to_integer(old(pool->checked_out)) - 1) <= 2147483647 by {
                close() using {  };
            }
            have to_integer(pool->checked_out) == (to_integer(old(pool->checked_out)) - 1) by {
                have pool->checked_out == old(pool->checked_out) - 1;
                rewrite(pool->checked_out, old(pool->checked_out) - 1);
                close();
            }
            have -2147483648 <= (to_integer(old(count(slot(pool)))) + 1) by {
                close() using { 0 <= to_integer(old(count(slot(pool)))); };
            }
            have (to_integer(old(count(slot(pool)))) + 1) <= 2147483647 by {
                close() using { to_integer((to_integer(old(count(slot(pool)))) + 1)) <= 2147483647; };
            }
            have to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool)))) + 1) by {
                close() using { -2147483648 <= (to_integer(old(count(slot(pool)))) + 1); (to_integer(old(count(slot(pool)))) + 1) <= 2147483647; };
            }
            have to_integer(pool->capacity) <= (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) by {
                close() using { at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool))))); to_integer(pool->checked_out) == (to_integer(old(pool->checked_out))
                        - 1); to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool))))
                        + 1); };
            }
            have (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) <= to_integer(pool->capacity) by {
                close() using { at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool))))); to_integer(pool->checked_out) == (to_integer(old(pool->checked_out))
                        - 1); to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool))))
                        + 1); };
            }
            close() using { to_integer(pool->capacity) <= (to_integer(pool->checked_out) +
                    to_integer(count(slot(pool)))); (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) <=
                    to_integer(pool->capacity); };
        }
    }
    step();
    close();
    have to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool)))) + 1) by {
        have -2147483648 <= (to_integer(old(count(slot(pool)))) + 1) by {
            close() using { 0 <= to_integer(old(count(slot(pool)))); };
        }
        have (to_integer(old(count(slot(pool)))) + 1) <= 2147483647 by {
            close() using { to_integer((to_integer(old(count(slot(pool)))) + 1)) <= 2147483647; };
        }
        have to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool)))) + 1) by {
            close() using { -2147483648 <= (to_integer(old(count(slot(pool)))) + 1); (to_integer(old(count(slot(pool)))) + 1) <= 2147483647; };
        }
        close();
    }
    have to_integer(count(item(pool, _))) == (to_integer(old(count(item(pool, _)))) - 1) by {
        have to_integer(count(item(pool, _))) <= (to_integer(old(count(item(pool, _)))) - 1) by {
            close() using { at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool))))); at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer((pool->checked_out - 1)) + to_integer((old(count(slot(pool))) +
                    1)))); to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool)))) + 1); to_integer(old(pool->checked_out)) == to_integer(old(count(item(pool,
                    _)))); to_integer(pool->checked_out) == to_integer(count(item(pool, _))); to_integer(pool->checked_out) == to_integer(old(pool->checked_out) - 1); };
        }
        have (to_integer(old(count(item(pool, _)))) - 1) <= to_integer(count(item(pool, _))) by {
            close() using { at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool))))); at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer((pool->checked_out - 1)) + to_integer((old(count(slot(pool))) +
                    1)))); to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool)))) + 1); to_integer(old(pool->checked_out)) == to_integer(old(count(item(pool,
                    _)))); to_integer(pool->checked_out) == to_integer(count(item(pool, _))); to_integer(pool->checked_out) == to_integer(old(pool->checked_out) - 1); };
        }
        close() using { to_integer(count(item(pool, _))) <= (to_integer(old(count(item(pool, _)))) -
                1); (to_integer(old(count(item(pool, _)))) - 1) <= to_integer(count(item(pool,
                _))); };
    }
    have to_integer(pool->checked_out) == (to_integer(old(pool->checked_out)) - 1) by {
        close();
    }
    have defined((pool->checked_out + count(slot(pool)))) by {
        have (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) >= -2147483648 by {
            have 0 <= to_integer(count(slot(pool)));
            have 0 <= to_integer(pool->checked_out) + to_integer(count(slot(pool))) by {
                apply(integer::add_le(0, to_integer(pool->checked_out), 0, to_integer(count(slot(pool)))));
                close();
            }
            apply(integer::le_transitive(-2147483648, 0, to_integer(pool->checked_out) + to_integer(count(slot(pool)))));
        }
        have (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) <= 2147483647 by {
            close() using { at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer((pool->checked_out - 1)) + to_integer((old(count(slot(pool))) +
                    1)))); to_integer(pool->checked_out) == to_integer(old(pool->checked_out) - 1); };
        }
        close();
    }
    have to_integer(pool->capacity) == (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) by {
        close();
    }
    have 0 <= pool->checked_out and to_integer(pool->checked_out) == to_integer(count(item(pool, _))) and to_integer(pool->capacity) == (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) by {
        close();
    }
    close();
    close();
    close();
    close();
    close();
    close();
    close();
    close();
    have p->value == old(p->value) by close();
}
void pipeline(struct pool* pool, struct payload* first, struct payload* second) {
 consumes storage(pool);
 requires count(slot(pool)) == 0;
 requires count(item(pool, _)) == 0;
 owns *first; owns *second;
 produces control(pool);
 produces 2 of slot(pool);
} by {
    step();
    have to_integer(count(item(pool, _))) == 0 by {
        close();
    }
    have defined((count(item(pool, _)) + 1)) by {
        have (to_integer(count(item(pool, _))) + to_integer(1)) >= -2147483648 by {
            close() using { 0 <= to_integer(count(item(pool, _))); };
        }
        have (to_integer(count(item(pool, _))) + to_integer(1)) <= 2147483647 by {
            close() using { to_integer(count(item(pool, _))) == 0; };
        }
        close();
    }
    step();
    have to_integer(count(item(pool, first))) == 1 by {
        close();
    }
    step();
    step();
}
```

```expect
pass
```
