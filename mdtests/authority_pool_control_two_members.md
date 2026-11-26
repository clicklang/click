# Two checked-out private members

```c filename=pool.c
struct pool { int32 checked_out; int32 capacity; };
struct payload { int32 value; };
void initialize(struct pool* pool, int32 amount) { pool->checked_out=0; pool->capacity=amount; }
void checkout(struct pool* pool, struct payload* p) { pool->checked_out=pool->checked_out+1; }
void give_back(struct pool* pool, struct payload* p) { pool->checked_out=pool->checked_out-1; }
void pipeline(struct pool* pool, struct payload* first, struct payload* second) {
 initialize(pool,2); checkout(pool,first); checkout(pool,second);
 first->value=11; second->value=22;
 give_back(pool,second); give_back(pool,first);
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
predicate valid_pool(pool: struct pool*) {
    0 <= pool->checked_out and
    pool->checked_out == count(item(pool, _)) and
    pool->capacity == pool->checked_out + count(slot(pool))
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
    ensures valid_pool(pool);
} by {
    unfold(storage(pool));
    step();
    step();
    fold(amount of slot(pool));
    fold(control(pool));
    step();
    unfold(valid_pool(pool));
    close();
    unfold(valid_pool(pool));
    have to_integer(count(item(pool, _))) == 0 by {
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
    ensures valid_pool(pool);
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
        have p->value == old(p->value) by close();
        apply(integer::int32_subtract_to_integer(pool->checked_out, 1));
        mark before_decrement;
        step();
        have separate(statement(0).footprint, memory(p->value)) by {
            close() using { separate(memory(p->value), memory(pool->checked_out)); };
        }
        have p->value == at(before_decrement, p->value) by {
            preserve(memory(p->value), statement(0));
        }
        have p->value == old(p->value) by {
            rewrite(p->value, at(before_decrement, p->value)); close();
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
    unfold(valid_pool(pool));
    close();
    unfold(valid_pool(pool));
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
    have valid_pool(pool) by { unfold(valid_pool(pool)); close(); }
    close();
    close();
    close();
    close();
    close();
}
void pipeline(struct pool* pool, struct payload* first, struct payload* second) {
 consumes storage(pool);
 requires count(slot(pool)) == 0;
 requires count(item(pool, _)) == 0;
 owns *first; owns *second;
 produces control(pool);
 produces 2 of slot(pool);
 ensures pool->checked_out == 0;
 ensures pool->capacity == 2;
 ensures first->value == 11;
 ensures second->value == 22;
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
    have to_integer(count(item(pool, _))) == 1 by {
        close();
    }
    have defined((count(item(pool, _)) + 1)) by {
        have (to_integer(count(item(pool, _))) + to_integer(1)) >= -2147483648 by {
            close() using { to_integer(count(item(pool, _))) == 1; };
        }
        have (to_integer(count(item(pool, _))) + to_integer(1)) <= 2147483647 by {
            close() using { to_integer(count(item(pool, _))) == 1; };
        }
        close();
    }
    step();
    with(item(pool, first)) {
        step();
        have first->value == 11 by { close(); }
        // Keep both payload cells visible so the second store's frame is explicit.
        with(item(pool, second)) {
            have separate(memory(first->value), memory(second->value)) by { close(); }
            mark before_second;
            step();
            have separate(statement(4).footprint, memory(first->value)) by {
                close() using { separate(memory(first->value), memory(second->value)); };
            }
            have first->value == at(before_second, first->value) by {
                preserve(memory(first->value), statement(4));
            }
            have first->value == 11 by {
                rewrite(first->value, at(before_second, first->value));
                close();
            }
            have second->value == 22 by { close(); }
        }
    }
    have to_integer(count(item(pool, second))) == 1 by {
        close();
    }
    step();
    have to_integer(count(item(pool, first))) == 1 by {
        close();
    }
    step();
    step();
    close();
    have pool->checked_out == 0 by {
        close();
    }
    have pool->capacity == 2 by {
        close();
    }
    have first->value == 11 by {
        close();
    }
    have second->value == 22 by {
        close();
    }
    close();
    close();
    close();
    close();
    close();
    close();
    close();
}
```

```expect
pass
```
