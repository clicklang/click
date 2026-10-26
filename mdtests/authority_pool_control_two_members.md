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
    unfold(valid_pool);
    assumption();
    unfold(valid_pool);
    have to_integer(count(item(pool, _))) == 0 by {
        assumption();
    }
    have 0 <= pool->checked_out and to_integer(pool->checked_out) == to_integer(count(item(pool, _))) and to_integer(pool->capacity) == (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) by {
        assumption();
    }
    assumption();
    normalize();
    normalize();
    assumption();
    assumption();
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
    open(control(pool)) {
        have 1 <= to_integer(count(slot(pool))) by {
            assumption();
        }
        have defined((pool->checked_out + 1)) by {
            arithmetic_certificate rules {
                premise 0: at(function.entry, pool->checked_out) < at(function.entry, 2147483647) =>
                    at(function.entry, pool->checked_out) < at(function.entry, 2147483647);
                int32_defined bounds [0] => defined((pool->checked_out + 1));
                conclusion 0;
            }
        }
        unfold(slot(pool));
        step();
        fold(item(pool, p));
        have to_integer(pool->capacity) == (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) by {
            have -2147483648 <= (to_integer(old(pool->checked_out)) + 1) by {
                arithmetic_certificate {
                    negated_goal => (to_integer(old(pool->checked_out)) + 1) < -2147483648;
                    premise 0: 0 <= to_integer(old(pool->checked_out)) => 0 <=
                        to_integer(old(pool->checked_out));
                    add 0, 1 => (to_integer(old(pool->checked_out)) + 1 + 0) < (-2147483648 +
                        to_integer(old(pool->checked_out)));
                    conclusion 2;
                }
            }
            have (to_integer(old(pool->checked_out)) + 1) <= 2147483647 by {
                arithmetic_certificate {
                    negated_goal => 2147483647 < (to_integer(old(pool->checked_out)) + 1);
                    premise 0: to_integer(old(pool->checked_out)) < 2147483647 =>
                        to_integer(old(pool->checked_out)) < 2147483647;
                    add 0, 1 => (2147483647 + 1 + (to_integer(old(pool->checked_out)) + 1)) <=
                        (to_integer(old(pool->checked_out)) + 1 + 2147483647);
                    conclusion 2;
                }
            }
            have to_integer(pool->checked_out) == (to_integer(old(pool->checked_out)) + 1) by {
                arithmetic_certificate rules {
                    premise 0: -2147483648 <= (to_integer(old(pool->checked_out)) + 1) =>
                        -2147483648 <= (to_integer(old(pool->checked_out)) + 1);
                    premise 1: (to_integer(old(pool->checked_out)) + 1) <= 2147483647 =>
                        (to_integer(old(pool->checked_out)) + 1) <= 2147483647;
                    integer_operation_identity bounds [0, 1] => to_integer(pool->checked_out) ==
                        (to_integer(old(pool->checked_out)) + 1);
                    conclusion 0;
                }
            }
            have -2147483648 <= (to_integer(old(count(slot(pool)))) - 1) by {
                arithmetic_certificate {
                    negated_goal => (to_integer(old(count(slot(pool)))) - 1) < -2147483648;
                    premise 0: 1 <= to_integer(old(count(slot(pool)))) => 1 <=
                        to_integer(old(count(slot(pool))));
                    add 0, 1 => ((to_integer(old(count(slot(pool)))) - 1) + 1) < (-2147483648 +
                        to_integer(old(count(slot(pool)))));
                    conclusion 2;
                }
            }
            have (to_integer(old(count(slot(pool)))) - 1) <= 2147483647 by {
                arithmetic_certificate {
                    negated_goal => 2147483647 < (to_integer(old(count(slot(pool)))) - 1);
                    type_range => to_integer(old(count(slot(pool)))) <= 2147483647;
                    add 0, 1 => (2147483647 + to_integer(old(count(slot(pool))))) <
                        ((to_integer(old(count(slot(pool)))) - 1) + 2147483647);
                    conclusion 2;
                }
            }
            have to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool)))) - 1) by {
                arithmetic_certificate rules {
                    premise 0: -2147483648 <= (to_integer(old(count(slot(pool)))) - 1) =>
                        -2147483648 <= (to_integer(old(count(slot(pool)))) - 1);
                    premise 1: (to_integer(old(count(slot(pool)))) - 1) <= 2147483647 =>
                        (to_integer(old(count(slot(pool)))) - 1) <= 2147483647;
                    integer_operation_identity bounds [0, 1] => to_integer(count(slot(pool))) ==
                        (to_integer(old(count(slot(pool)))) - 1);
                    conclusion 0;
                }
            }
            have to_integer(pool->capacity) <= (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) by {
                arithmetic_certificate {
                    negated_goal => (to_integer(pool->checked_out) + to_integer(count(slot(pool))))
                        < to_integer(pool->capacity);
                    premise 0: at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) =>
                        at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool)))));
                    less_equal_from_equal 1 => at(function.entry, to_integer(pool->capacity)) <=
                        at(function.entry, (to_integer(pool->checked_out) +
                        to_integer(count(slot(pool)))));
                    premise 1: to_integer(pool->checked_out) == (to_integer(old(pool->checked_out))
                        + 1) => to_integer(pool->checked_out) == (to_integer(old(pool->checked_out))
                        + 1);
                    less_equal_from_equal 3 reverse => (to_integer(old(pool->checked_out)) + 1) <=
                        to_integer(pool->checked_out);
                    premise 2: to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool))))
                        - 1) => to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool))))
                        - 1);
                    less_equal_from_equal 5 reverse => (to_integer(old(count(slot(pool)))) - 1) <=
                        to_integer(count(slot(pool)));
                    add 0, 2 => (to_integer(pool->checked_out) + to_integer(count(slot(pool))) +
                        at(function.entry, to_integer(pool->capacity))) <
                        (to_integer(pool->capacity) + at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool))))));
                    add 7, 4 => (to_integer(pool->checked_out) + to_integer(count(slot(pool))) +
                        at(function.entry, to_integer(pool->capacity)) +
                        (to_integer(old(pool->checked_out)) + 1)) < (to_integer(pool->capacity) +
                        at(function.entry, (to_integer(pool->checked_out) +
                        to_integer(count(slot(pool))))) + to_integer(pool->checked_out));
                    add 8, 6 => (to_integer(pool->checked_out) + to_integer(count(slot(pool))) +
                        at(function.entry, to_integer(pool->capacity)) +
                        (to_integer(old(pool->checked_out)) + 1) +
                        (to_integer(old(count(slot(pool)))) - 1)) < (to_integer(pool->capacity) +
                        at(function.entry, (to_integer(pool->checked_out) +
                        to_integer(count(slot(pool))))) + to_integer(pool->checked_out) +
                        to_integer(count(slot(pool))));
                    conclusion 9;
                }
            }
            have (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) <= to_integer(pool->capacity) by {
                arithmetic_certificate {
                    negated_goal => to_integer(pool->capacity) < (to_integer(pool->checked_out) +
                        to_integer(count(slot(pool))));
                    premise 0: at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) =>
                        at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool)))));
                    less_equal_from_equal 1 reverse => at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) <=
                        at(function.entry, to_integer(pool->capacity));
                    premise 1: to_integer(pool->checked_out) == (to_integer(old(pool->checked_out))
                        + 1) => to_integer(pool->checked_out) == (to_integer(old(pool->checked_out))
                        + 1);
                    less_equal_from_equal 3 => to_integer(pool->checked_out) <=
                        (to_integer(old(pool->checked_out)) + 1);
                    premise 2: to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool))))
                        - 1) => to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool))))
                        - 1);
                    less_equal_from_equal 5 => to_integer(count(slot(pool))) <=
                        (to_integer(old(count(slot(pool)))) - 1);
                    add 0, 2 => (to_integer(pool->capacity) + at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool)))))) <
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool))) +
                        at(function.entry, to_integer(pool->capacity)));
                    add 7, 4 => (to_integer(pool->capacity) + at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) +
                        to_integer(pool->checked_out)) < (to_integer(pool->checked_out) +
                        to_integer(count(slot(pool))) + at(function.entry,
                        to_integer(pool->capacity)) + (to_integer(old(pool->checked_out)) + 1));
                    add 8, 6 => (to_integer(pool->capacity) + at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) +
                        to_integer(pool->checked_out) + to_integer(count(slot(pool)))) <
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool))) +
                        at(function.entry, to_integer(pool->capacity)) +
                        (to_integer(old(pool->checked_out)) + 1) +
                        (to_integer(old(count(slot(pool)))) - 1));
                    conclusion 9;
                }
            }
            arithmetic_certificate {
                premise 0: to_integer(pool->capacity) <= (to_integer(pool->checked_out) +
                    to_integer(count(slot(pool)))) => to_integer(pool->capacity) <=
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool))));
                premise 1: (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) <=
                    to_integer(pool->capacity) => (to_integer(pool->checked_out) +
                    to_integer(count(slot(pool)))) <= to_integer(pool->capacity);
                equal_from_bounds 0, 1 => to_integer(pool->capacity) ==
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool))));
                conclusion 2;
            }
        }
    }
    step();
    assumption();
    have to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool)))) - 1) by {
        have -2147483648 <= (to_integer(old(count(slot(pool)))) - 1) by {
            arithmetic_certificate {
                negated_goal => (to_integer(old(count(slot(pool)))) - 1) < -2147483648;
                premise 0: 1 <= to_integer(old(count(slot(pool)))) => 1 <=
                    to_integer(old(count(slot(pool))));
                add 0, 1 => ((to_integer(old(count(slot(pool)))) - 1) + 1) < (-2147483648 +
                    to_integer(old(count(slot(pool)))));
                conclusion 2;
            }
        }
        have (to_integer(old(count(slot(pool)))) - 1) <= 2147483647 by {
            arithmetic_certificate {
                negated_goal => 2147483647 < (to_integer(old(count(slot(pool)))) - 1);
                type_range => to_integer(old(count(slot(pool)))) <= 2147483647;
                add 0, 1 => (2147483647 + to_integer(old(count(slot(pool))))) <
                    ((to_integer(old(count(slot(pool)))) - 1) + 2147483647);
                conclusion 2;
            }
        }
        have to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool)))) - 1) by {
            arithmetic_certificate rules {
                premise 0: -2147483648 <= (to_integer(old(count(slot(pool)))) - 1) => -2147483648 <=
                    (to_integer(old(count(slot(pool)))) - 1);
                premise 1: (to_integer(old(count(slot(pool)))) - 1) <= 2147483647 =>
                    (to_integer(old(count(slot(pool)))) - 1) <= 2147483647;
                integer_operation_identity bounds [0, 1] => to_integer(count(slot(pool))) ==
                    (to_integer(old(count(slot(pool)))) - 1);
                conclusion 0;
            }
        }
        assumption();
    }
    have to_integer(count(item(pool, _))) == (to_integer(old(count(item(pool, _)))) + 1) by {
        have to_integer(count(item(pool, _))) <= (to_integer(old(count(item(pool, _)))) + 1) by {
            arithmetic_certificate {
                negated_goal => (to_integer(old(count(item(pool, _)))) + 1) <
                    to_integer(count(item(pool, _)));
                premise 0: at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) =>
                    at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool)))));
                less_equal_from_equal 1 => at(function.entry, to_integer(pool->capacity)) <=
                    at(function.entry, (to_integer(pool->checked_out) +
                    to_integer(count(slot(pool)))));
                premise 1: at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer((pool->checked_out + 1)) + to_integer((old(count(slot(pool))) -
                    1)))) => at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer((pool->checked_out + 1)) + to_integer((old(count(slot(pool))) -
                    1))));
                less_equal_from_equal 3 reverse => at(function.entry, (to_integer((pool->checked_out
                    + 1)) + to_integer((old(count(slot(pool))) - 1)))) <= at(function.entry,
                    to_integer(pool->capacity));
                premise 2: to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool)))) - 1)
                    => to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool)))) - 1);
                less_equal_from_equal 5 reverse => (to_integer(old(count(slot(pool)))) - 1) <=
                    to_integer(count(slot(pool)));
                premise 3: to_integer(old(pool->checked_out)) == to_integer(old(count(item(pool,
                    _)))) => to_integer(old(pool->checked_out)) == to_integer(old(count(item(pool,
                    _))));
                less_equal_from_equal 7 => to_integer(old(pool->checked_out)) <=
                    to_integer(old(count(item(pool, _))));
                premise 4: to_integer(pool->checked_out) == to_integer(count(item(pool, _))) =>
                    to_integer(pool->checked_out) == to_integer(count(item(pool, _)));
                less_equal_from_equal 9 reverse => to_integer(count(item(pool, _))) <=
                    to_integer(pool->checked_out);
                add 0, 2 => (to_integer(old(count(item(pool, _)))) + 1 + at(function.entry,
                    to_integer(pool->capacity))) < (to_integer(count(item(pool, _))) +
                    at(function.entry, (to_integer(pool->checked_out) +
                    to_integer(count(slot(pool))))));
                add 11, 4 => (to_integer(old(count(item(pool, _)))) + 1 + at(function.entry,
                    to_integer(pool->capacity)) + at(function.entry, (to_integer((pool->checked_out
                    + 1)) + to_integer((old(count(slot(pool))) - 1))))) <
                    (to_integer(count(item(pool, _))) + at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) +
                    at(function.entry, to_integer(pool->capacity)));
                add 12, 6 => (to_integer(old(count(item(pool, _)))) + 1 + at(function.entry,
                    to_integer(pool->capacity)) + at(function.entry, (to_integer((pool->checked_out
                    + 1)) + to_integer((old(count(slot(pool))) - 1)))) +
                    (to_integer(old(count(slot(pool)))) - 1)) < (to_integer(count(item(pool, _))) +
                    at(function.entry, (to_integer(pool->checked_out) +
                    to_integer(count(slot(pool))))) + at(function.entry, to_integer(pool->capacity))
                    + to_integer(count(slot(pool))));
                add 13, 8 => (to_integer(old(count(item(pool, _)))) + 1 + at(function.entry,
                    to_integer(pool->capacity)) + at(function.entry, (to_integer((pool->checked_out
                    + 1)) + to_integer((old(count(slot(pool))) - 1)))) +
                    (to_integer(old(count(slot(pool)))) - 1) + to_integer(old(pool->checked_out))) <
                    (to_integer(count(item(pool, _))) + at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) +
                    at(function.entry, to_integer(pool->capacity)) + to_integer(count(slot(pool))) +
                    to_integer(old(count(item(pool, _)))));
                add 14, 10 => (to_integer(old(count(item(pool, _)))) + 1 + at(function.entry,
                    to_integer(pool->capacity)) + at(function.entry, (to_integer((pool->checked_out
                    + 1)) + to_integer((old(count(slot(pool))) - 1)))) +
                    (to_integer(old(count(slot(pool)))) - 1) + to_integer(old(pool->checked_out)) +
                    to_integer(count(item(pool, _)))) < (to_integer(count(item(pool, _))) +
                    at(function.entry, (to_integer(pool->checked_out) +
                    to_integer(count(slot(pool))))) + at(function.entry, to_integer(pool->capacity))
                    + to_integer(count(slot(pool))) + to_integer(old(count(item(pool, _)))) +
                    to_integer(pool->checked_out));
                conclusion 15;
            }
        }
        have (to_integer(old(count(item(pool, _)))) + 1) <= to_integer(count(item(pool, _))) by {
            arithmetic_certificate {
                negated_goal => to_integer(count(item(pool, _))) < (to_integer(old(count(item(pool,
                    _)))) + 1);
                premise 0: at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) =>
                    at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool)))));
                less_equal_from_equal 1 reverse => at(function.entry, (to_integer(pool->checked_out)
                    + to_integer(count(slot(pool))))) <= at(function.entry,
                    to_integer(pool->capacity));
                premise 1: at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer((pool->checked_out + 1)) + to_integer((old(count(slot(pool))) -
                    1)))) => at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer((pool->checked_out + 1)) + to_integer((old(count(slot(pool))) -
                    1))));
                less_equal_from_equal 3 => at(function.entry, to_integer(pool->capacity)) <=
                    at(function.entry, (to_integer((pool->checked_out + 1)) +
                    to_integer((old(count(slot(pool))) - 1))));
                premise 2: to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool)))) - 1)
                    => to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool)))) - 1);
                less_equal_from_equal 5 => to_integer(count(slot(pool))) <=
                    (to_integer(old(count(slot(pool)))) - 1);
                premise 3: to_integer(old(pool->checked_out)) == to_integer(old(count(item(pool,
                    _)))) => to_integer(old(pool->checked_out)) == to_integer(old(count(item(pool,
                    _))));
                less_equal_from_equal 7 reverse => to_integer(old(count(item(pool, _)))) <=
                    to_integer(old(pool->checked_out));
                premise 4: to_integer(pool->checked_out) == to_integer(count(item(pool, _))) =>
                    to_integer(pool->checked_out) == to_integer(count(item(pool, _)));
                less_equal_from_equal 9 => to_integer(pool->checked_out) <=
                    to_integer(count(item(pool, _)));
                add 0, 2 => (to_integer(count(item(pool, _))) + at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool)))))) <
                    (to_integer(old(count(item(pool, _)))) + 1 + at(function.entry,
                    to_integer(pool->capacity)));
                add 11, 4 => (to_integer(count(item(pool, _))) + at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) +
                    at(function.entry, to_integer(pool->capacity))) <
                    (to_integer(old(count(item(pool, _)))) + 1 + at(function.entry,
                    to_integer(pool->capacity)) + at(function.entry, (to_integer((pool->checked_out
                    + 1)) + to_integer((old(count(slot(pool))) - 1)))));
                add 12, 6 => (to_integer(count(item(pool, _))) + at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) +
                    at(function.entry, to_integer(pool->capacity)) + to_integer(count(slot(pool))))
                    < (to_integer(old(count(item(pool, _)))) + 1 + at(function.entry,
                    to_integer(pool->capacity)) + at(function.entry, (to_integer((pool->checked_out
                    + 1)) + to_integer((old(count(slot(pool))) - 1)))) +
                    (to_integer(old(count(slot(pool)))) - 1));
                add 13, 8 => (to_integer(count(item(pool, _))) + at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) +
                    at(function.entry, to_integer(pool->capacity)) + to_integer(count(slot(pool))) +
                    to_integer(old(count(item(pool, _))))) < (to_integer(old(count(item(pool, _))))
                    + 1 + at(function.entry, to_integer(pool->capacity)) + at(function.entry,
                    (to_integer((pool->checked_out + 1)) + to_integer((old(count(slot(pool))) -
                    1)))) + (to_integer(old(count(slot(pool)))) - 1) +
                    to_integer(old(pool->checked_out)));
                add 14, 10 => (to_integer(count(item(pool, _))) + at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) +
                    at(function.entry, to_integer(pool->capacity)) + to_integer(count(slot(pool))) +
                    to_integer(old(count(item(pool, _)))) + to_integer(pool->checked_out)) <
                    (to_integer(old(count(item(pool, _)))) + 1 + at(function.entry,
                    to_integer(pool->capacity)) + at(function.entry, (to_integer((pool->checked_out
                    + 1)) + to_integer((old(count(slot(pool))) - 1)))) +
                    (to_integer(old(count(slot(pool)))) - 1) + to_integer(old(pool->checked_out)) +
                    to_integer(count(item(pool, _))));
                conclusion 15;
            }
        }
        arithmetic_certificate {
            premise 0: to_integer(count(item(pool, _))) <= (to_integer(old(count(item(pool, _)))) +
                1) => to_integer(count(item(pool, _))) <= (to_integer(old(count(item(pool, _)))) +
                1);
            premise 1: (to_integer(old(count(item(pool, _)))) + 1) <= to_integer(count(item(pool,
                _))) => (to_integer(old(count(item(pool, _)))) + 1) <= to_integer(count(item(pool,
                _)));
            equal_from_bounds 0, 1 => to_integer(count(item(pool, _))) ==
                (to_integer(old(count(item(pool, _)))) + 1);
            conclusion 2;
        }
    }
    have to_integer(pool->checked_out) == (to_integer(old(pool->checked_out)) + 1) by {
        assumption();
    }
    assumption();
    assumption();
    assumption();
    assumption();
    normalize();
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
    open(control(pool)) {
        have 1 <= to_integer(count(item(pool, _))) by {
            assumption();
        }
        have 1 <= pool->checked_out by {
            rewrite(to_integer(pool->checked_out) == to_integer(count(item(pool, _))));
            assumption();
        }
        have defined((count(slot(pool)) + 1)) by {
            have (to_integer(count(slot(pool))) + to_integer(1)) >= -2147483648 by {
                arithmetic_certificate {
                    negated_goal => (to_integer(count(slot(pool))) + to_integer(1)) < -2147483648;
                    premise 0: 0 <= to_integer(count(slot(pool))) => 0 <=
                        to_integer(count(slot(pool)));
                    add 0, 1 => (to_integer(count(slot(pool))) + to_integer(1) + 0) < (-2147483648 +
                        to_integer(count(slot(pool))));
                    conclusion 2;
                }
            }
            have (to_integer(count(slot(pool))) + to_integer(1)) <= 2147483647 by {
                arithmetic_certificate {
                    negated_goal => 2147483647 < (to_integer(count(slot(pool))) + to_integer(1));
                    premise 0: at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) =>
                        at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool)))));
                    less_equal_from_equal 1 reverse => at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) <=
                        at(function.entry, to_integer(pool->capacity));
                    premise 1: 1 <= to_integer(pool->checked_out) => 1 <=
                        to_integer(pool->checked_out);
                    type_range => to_integer(at(function.entry, to_integer(pool->capacity))) <=
                        2147483647;
                    add 0, 2 => (2147483647 + at(function.entry, (to_integer(pool->checked_out) +
                        to_integer(count(slot(pool)))))) < (to_integer(count(slot(pool))) +
                        to_integer(1) + at(function.entry, to_integer(pool->capacity)));
                    add 5, 3 => (2147483647 + at(function.entry, (to_integer(pool->checked_out) +
                        to_integer(count(slot(pool))))) + 1) < (to_integer(count(slot(pool))) +
                        to_integer(1) + at(function.entry, to_integer(pool->capacity)) +
                        to_integer(pool->checked_out));
                    add 6, 4 => (2147483647 + at(function.entry, (to_integer(pool->checked_out) +
                        to_integer(count(slot(pool))))) + 1 + to_integer(at(function.entry,
                        to_integer(pool->capacity)))) < (to_integer(count(slot(pool))) +
                        to_integer(1) + at(function.entry, to_integer(pool->capacity)) +
                        to_integer(pool->checked_out) + 2147483647);
                    conclusion 7;
                }
            }
            assumption();
        }
        unfold(item(pool, p));
        step();
        fold(slot(pool));
        have 0 <= pool->checked_out by {
            arithmetic_certificate signed_int32 {
                premise 0: at(function.entry, 1) <= at(function.entry, pool->checked_out) =>
                    at(function.entry, 1) <= at(function.entry, pool->checked_out);
                interval_from_affine 0 (at(function.entry, pool->checked_out)) (1) (2147483647);
                interval_atom (1) (1) (1);
                interval_subtract 1, 2 1 (0) (2147483646);
                affine_conclusion 0 3 => (0 as int32) <= (pool->checked_out as int32);
                conclusion 4;
            }
        }
        have to_integer(pool->checked_out) == to_integer(count(item(pool, _))) by {
            assumption();
        }
        have to_integer(pool->capacity) == (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) by {
            have -2147483648 <= (to_integer(old(pool->checked_out)) - 1) by {
                arithmetic_certificate {
                    negated_goal => (to_integer(old(pool->checked_out)) - 1) < -2147483648;
                    premise 0: 0 <= to_integer(old(pool->checked_out)) => 0 <=
                        to_integer(old(pool->checked_out));
                    add 0, 1 => ((to_integer(old(pool->checked_out)) - 1) + 0) < (-2147483648 +
                        to_integer(old(pool->checked_out)));
                    conclusion 2;
                }
            }
            have (to_integer(old(pool->checked_out)) - 1) <= 2147483647 by {
                arithmetic_certificate {
                    negated_goal => 2147483647 < (to_integer(old(pool->checked_out)) - 1);
                    type_range => to_integer(old(pool->checked_out)) <= 2147483647;
                    add 0, 1 => (2147483647 + to_integer(old(pool->checked_out))) <
                        ((to_integer(old(pool->checked_out)) - 1) + 2147483647);
                    conclusion 2;
                }
            }
            have to_integer(pool->checked_out) == (to_integer(old(pool->checked_out)) - 1) by {
                arithmetic_certificate rules {
                    premise 0: -2147483648 <= (to_integer(old(pool->checked_out)) - 1) =>
                        -2147483648 <= (to_integer(old(pool->checked_out)) - 1);
                    premise 1: (to_integer(old(pool->checked_out)) - 1) <= 2147483647 =>
                        (to_integer(old(pool->checked_out)) - 1) <= 2147483647;
                    integer_operation_identity bounds [0, 1] => to_integer(pool->checked_out) ==
                        (to_integer(old(pool->checked_out)) - 1);
                    conclusion 0;
                }
            }
            have -2147483648 <= (to_integer(old(count(slot(pool)))) + 1) by {
                arithmetic_certificate {
                    negated_goal => (to_integer(old(count(slot(pool)))) + 1) < -2147483648;
                    premise 0: 0 <= to_integer(old(count(slot(pool)))) => 0 <=
                        to_integer(old(count(slot(pool))));
                    add 0, 1 => (to_integer(old(count(slot(pool)))) + 1 + 0) < (-2147483648 +
                        to_integer(old(count(slot(pool)))));
                    conclusion 2;
                }
            }
            have (to_integer(old(count(slot(pool)))) + 1) <= 2147483647 by {
                arithmetic_certificate {
                    negated_goal => 2147483647 < (to_integer(old(count(slot(pool)))) + 1);
                    premise 0: to_integer((to_integer(old(count(slot(pool)))) + 1)) <= 2147483647 =>
                        to_integer((to_integer(old(count(slot(pool)))) + 1)) <= 2147483647;
                    add 0, 1 => (2147483647 + to_integer((to_integer(old(count(slot(pool)))) + 1)))
                        < (to_integer(old(count(slot(pool)))) + 1 + 2147483647);
                    conclusion 2;
                }
            }
            have to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool)))) + 1) by {
                arithmetic_certificate rules {
                    premise 0: -2147483648 <= (to_integer(old(count(slot(pool)))) + 1) =>
                        -2147483648 <= (to_integer(old(count(slot(pool)))) + 1);
                    premise 1: (to_integer(old(count(slot(pool)))) + 1) <= 2147483647 =>
                        (to_integer(old(count(slot(pool)))) + 1) <= 2147483647;
                    integer_operation_identity bounds [0, 1] => to_integer(count(slot(pool))) ==
                        (to_integer(old(count(slot(pool)))) + 1);
                    conclusion 0;
                }
            }
            have to_integer(pool->capacity) <= (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) by {
                arithmetic_certificate {
                    negated_goal => (to_integer(pool->checked_out) + to_integer(count(slot(pool))))
                        < to_integer(pool->capacity);
                    premise 0: at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) =>
                        at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool)))));
                    less_equal_from_equal 1 => at(function.entry, to_integer(pool->capacity)) <=
                        at(function.entry, (to_integer(pool->checked_out) +
                        to_integer(count(slot(pool)))));
                    premise 1: to_integer(pool->checked_out) == (to_integer(old(pool->checked_out))
                        - 1) => to_integer(pool->checked_out) == (to_integer(old(pool->checked_out))
                        - 1);
                    less_equal_from_equal 3 reverse => (to_integer(old(pool->checked_out)) - 1) <=
                        to_integer(pool->checked_out);
                    premise 2: to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool))))
                        + 1) => to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool))))
                        + 1);
                    less_equal_from_equal 5 reverse => (to_integer(old(count(slot(pool)))) + 1) <=
                        to_integer(count(slot(pool)));
                    add 0, 2 => (to_integer(pool->checked_out) + to_integer(count(slot(pool))) +
                        at(function.entry, to_integer(pool->capacity))) <
                        (to_integer(pool->capacity) + at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool))))));
                    add 7, 4 => (to_integer(pool->checked_out) + to_integer(count(slot(pool))) +
                        at(function.entry, to_integer(pool->capacity)) +
                        (to_integer(old(pool->checked_out)) - 1)) < (to_integer(pool->capacity) +
                        at(function.entry, (to_integer(pool->checked_out) +
                        to_integer(count(slot(pool))))) + to_integer(pool->checked_out));
                    add 8, 6 => (to_integer(pool->checked_out) + to_integer(count(slot(pool))) +
                        at(function.entry, to_integer(pool->capacity)) +
                        (to_integer(old(pool->checked_out)) - 1) +
                        (to_integer(old(count(slot(pool)))) + 1)) < (to_integer(pool->capacity) +
                        at(function.entry, (to_integer(pool->checked_out) +
                        to_integer(count(slot(pool))))) + to_integer(pool->checked_out) +
                        to_integer(count(slot(pool))));
                    conclusion 9;
                }
            }
            have (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) <= to_integer(pool->capacity) by {
                arithmetic_certificate {
                    negated_goal => to_integer(pool->capacity) < (to_integer(pool->checked_out) +
                        to_integer(count(slot(pool))));
                    premise 0: at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) =>
                        at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool)))));
                    less_equal_from_equal 1 reverse => at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) <=
                        at(function.entry, to_integer(pool->capacity));
                    premise 1: to_integer(pool->checked_out) == (to_integer(old(pool->checked_out))
                        - 1) => to_integer(pool->checked_out) == (to_integer(old(pool->checked_out))
                        - 1);
                    less_equal_from_equal 3 => to_integer(pool->checked_out) <=
                        (to_integer(old(pool->checked_out)) - 1);
                    premise 2: to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool))))
                        + 1) => to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool))))
                        + 1);
                    less_equal_from_equal 5 => to_integer(count(slot(pool))) <=
                        (to_integer(old(count(slot(pool)))) + 1);
                    add 0, 2 => (to_integer(pool->capacity) + at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool)))))) <
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool))) +
                        at(function.entry, to_integer(pool->capacity)));
                    add 7, 4 => (to_integer(pool->capacity) + at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) +
                        to_integer(pool->checked_out)) < (to_integer(pool->checked_out) +
                        to_integer(count(slot(pool))) + at(function.entry,
                        to_integer(pool->capacity)) + (to_integer(old(pool->checked_out)) - 1));
                    add 8, 6 => (to_integer(pool->capacity) + at(function.entry,
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) +
                        to_integer(pool->checked_out) + to_integer(count(slot(pool)))) <
                        (to_integer(pool->checked_out) + to_integer(count(slot(pool))) +
                        at(function.entry, to_integer(pool->capacity)) +
                        (to_integer(old(pool->checked_out)) - 1) +
                        (to_integer(old(count(slot(pool)))) + 1));
                    conclusion 9;
                }
            }
            arithmetic_certificate {
                premise 0: to_integer(pool->capacity) <= (to_integer(pool->checked_out) +
                    to_integer(count(slot(pool)))) => to_integer(pool->capacity) <=
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool))));
                premise 1: (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) <=
                    to_integer(pool->capacity) => (to_integer(pool->checked_out) +
                    to_integer(count(slot(pool)))) <= to_integer(pool->capacity);
                equal_from_bounds 0, 1 => to_integer(pool->capacity) ==
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool))));
                conclusion 2;
            }
        }
    }
    step();
    unfold(valid_pool);
    assumption();
    unfold(valid_pool);
    have to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool)))) + 1) by {
        have -2147483648 <= (to_integer(old(count(slot(pool)))) + 1) by {
            arithmetic_certificate {
                negated_goal => (to_integer(old(count(slot(pool)))) + 1) < -2147483648;
                premise 0: 0 <= to_integer(old(count(slot(pool)))) => 0 <=
                    to_integer(old(count(slot(pool))));
                add 0, 1 => (to_integer(old(count(slot(pool)))) + 1 + 0) < (-2147483648 +
                    to_integer(old(count(slot(pool)))));
                conclusion 2;
            }
        }
        have (to_integer(old(count(slot(pool)))) + 1) <= 2147483647 by {
            arithmetic_certificate {
                negated_goal => 2147483647 < (to_integer(old(count(slot(pool)))) + 1);
                premise 0: to_integer((to_integer(old(count(slot(pool)))) + 1)) <= 2147483647 =>
                    to_integer((to_integer(old(count(slot(pool)))) + 1)) <= 2147483647;
                add 0, 1 => (2147483647 + to_integer((to_integer(old(count(slot(pool)))) + 1))) <
                    (to_integer(old(count(slot(pool)))) + 1 + 2147483647);
                conclusion 2;
            }
        }
        have to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool)))) + 1) by {
            arithmetic_certificate rules {
                premise 0: -2147483648 <= (to_integer(old(count(slot(pool)))) + 1) => -2147483648 <=
                    (to_integer(old(count(slot(pool)))) + 1);
                premise 1: (to_integer(old(count(slot(pool)))) + 1) <= 2147483647 =>
                    (to_integer(old(count(slot(pool)))) + 1) <= 2147483647;
                integer_operation_identity bounds [0, 1] => to_integer(count(slot(pool))) ==
                    (to_integer(old(count(slot(pool)))) + 1);
                conclusion 0;
            }
        }
        assumption();
    }
    have to_integer(count(item(pool, _))) == (to_integer(old(count(item(pool, _)))) - 1) by {
        have to_integer(count(item(pool, _))) <= (to_integer(old(count(item(pool, _)))) - 1) by {
            arithmetic_certificate {
                negated_goal => (to_integer(old(count(item(pool, _)))) - 1) <
                    to_integer(count(item(pool, _)));
                premise 0: at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) =>
                    at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool)))));
                less_equal_from_equal 1 => at(function.entry, to_integer(pool->capacity)) <=
                    at(function.entry, (to_integer(pool->checked_out) +
                    to_integer(count(slot(pool)))));
                premise 1: at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer((pool->checked_out - 1)) + to_integer((old(count(slot(pool))) +
                    1)))) => at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer((pool->checked_out - 1)) + to_integer((old(count(slot(pool))) +
                    1))));
                less_equal_from_equal 3 reverse => at(function.entry, (to_integer((pool->checked_out
                    - 1)) + to_integer((old(count(slot(pool))) + 1)))) <= at(function.entry,
                    to_integer(pool->capacity));
                premise 2: to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool)))) + 1)
                    => to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool)))) + 1);
                less_equal_from_equal 5 reverse => (to_integer(old(count(slot(pool)))) + 1) <=
                    to_integer(count(slot(pool)));
                premise 3: to_integer(old(pool->checked_out)) == to_integer(old(count(item(pool,
                    _)))) => to_integer(old(pool->checked_out)) == to_integer(old(count(item(pool,
                    _))));
                less_equal_from_equal 7 => to_integer(old(pool->checked_out)) <=
                    to_integer(old(count(item(pool, _))));
                premise 4: to_integer(pool->checked_out) == to_integer(count(item(pool, _))) =>
                    to_integer(pool->checked_out) == to_integer(count(item(pool, _)));
                less_equal_from_equal 9 reverse => to_integer(count(item(pool, _))) <=
                    to_integer(pool->checked_out);
                add 0, 2 => ((to_integer(old(count(item(pool, _)))) - 1) + at(function.entry,
                    to_integer(pool->capacity))) < (to_integer(count(item(pool, _))) +
                    at(function.entry, (to_integer(pool->checked_out) +
                    to_integer(count(slot(pool))))));
                add 11, 4 => ((to_integer(old(count(item(pool, _)))) - 1) + at(function.entry,
                    to_integer(pool->capacity)) + at(function.entry, (to_integer((pool->checked_out
                    - 1)) + to_integer((old(count(slot(pool))) + 1))))) <
                    (to_integer(count(item(pool, _))) + at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) +
                    at(function.entry, to_integer(pool->capacity)));
                add 12, 6 => ((to_integer(old(count(item(pool, _)))) - 1) + at(function.entry,
                    to_integer(pool->capacity)) + at(function.entry, (to_integer((pool->checked_out
                    - 1)) + to_integer((old(count(slot(pool))) + 1)))) +
                    (to_integer(old(count(slot(pool)))) + 1)) < (to_integer(count(item(pool, _))) +
                    at(function.entry, (to_integer(pool->checked_out) +
                    to_integer(count(slot(pool))))) + at(function.entry, to_integer(pool->capacity))
                    + to_integer(count(slot(pool))));
                add 13, 8 => ((to_integer(old(count(item(pool, _)))) - 1) + at(function.entry,
                    to_integer(pool->capacity)) + at(function.entry, (to_integer((pool->checked_out
                    - 1)) + to_integer((old(count(slot(pool))) + 1)))) +
                    (to_integer(old(count(slot(pool)))) + 1) + to_integer(old(pool->checked_out))) <
                    (to_integer(count(item(pool, _))) + at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) +
                    at(function.entry, to_integer(pool->capacity)) + to_integer(count(slot(pool))) +
                    to_integer(old(count(item(pool, _)))));
                add 14, 10 => ((to_integer(old(count(item(pool, _)))) - 1) + at(function.entry,
                    to_integer(pool->capacity)) + at(function.entry, (to_integer((pool->checked_out
                    - 1)) + to_integer((old(count(slot(pool))) + 1)))) +
                    (to_integer(old(count(slot(pool)))) + 1) + to_integer(old(pool->checked_out)) +
                    to_integer(count(item(pool, _)))) < (to_integer(count(item(pool, _))) +
                    at(function.entry, (to_integer(pool->checked_out) +
                    to_integer(count(slot(pool))))) + at(function.entry, to_integer(pool->capacity))
                    + to_integer(count(slot(pool))) + to_integer(old(count(item(pool, _)))) +
                    to_integer(pool->checked_out));
                conclusion 15;
            }
        }
        have (to_integer(old(count(item(pool, _)))) - 1) <= to_integer(count(item(pool, _))) by {
            arithmetic_certificate {
                negated_goal => to_integer(count(item(pool, _))) < (to_integer(old(count(item(pool,
                    _)))) - 1);
                premise 0: at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) =>
                    at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool)))));
                less_equal_from_equal 1 reverse => at(function.entry, (to_integer(pool->checked_out)
                    + to_integer(count(slot(pool))))) <= at(function.entry,
                    to_integer(pool->capacity));
                premise 1: at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer((pool->checked_out - 1)) + to_integer((old(count(slot(pool))) +
                    1)))) => at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer((pool->checked_out - 1)) + to_integer((old(count(slot(pool))) +
                    1))));
                less_equal_from_equal 3 => at(function.entry, to_integer(pool->capacity)) <=
                    at(function.entry, (to_integer((pool->checked_out - 1)) +
                    to_integer((old(count(slot(pool))) + 1))));
                premise 2: to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool)))) + 1)
                    => to_integer(count(slot(pool))) == (to_integer(old(count(slot(pool)))) + 1);
                less_equal_from_equal 5 => to_integer(count(slot(pool))) <=
                    (to_integer(old(count(slot(pool)))) + 1);
                premise 3: to_integer(old(pool->checked_out)) == to_integer(old(count(item(pool,
                    _)))) => to_integer(old(pool->checked_out)) == to_integer(old(count(item(pool,
                    _))));
                less_equal_from_equal 7 reverse => to_integer(old(count(item(pool, _)))) <=
                    to_integer(old(pool->checked_out));
                premise 4: to_integer(pool->checked_out) == to_integer(count(item(pool, _))) =>
                    to_integer(pool->checked_out) == to_integer(count(item(pool, _)));
                less_equal_from_equal 9 => to_integer(pool->checked_out) <=
                    to_integer(count(item(pool, _)));
                add 0, 2 => (to_integer(count(item(pool, _))) + at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool)))))) <
                    ((to_integer(old(count(item(pool, _)))) - 1) + at(function.entry,
                    to_integer(pool->capacity)));
                add 11, 4 => (to_integer(count(item(pool, _))) + at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) +
                    at(function.entry, to_integer(pool->capacity))) <
                    ((to_integer(old(count(item(pool, _)))) - 1) + at(function.entry,
                    to_integer(pool->capacity)) + at(function.entry, (to_integer((pool->checked_out
                    - 1)) + to_integer((old(count(slot(pool))) + 1)))));
                add 12, 6 => (to_integer(count(item(pool, _))) + at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) +
                    at(function.entry, to_integer(pool->capacity)) + to_integer(count(slot(pool))))
                    < ((to_integer(old(count(item(pool, _)))) - 1) + at(function.entry,
                    to_integer(pool->capacity)) + at(function.entry, (to_integer((pool->checked_out
                    - 1)) + to_integer((old(count(slot(pool))) + 1)))) +
                    (to_integer(old(count(slot(pool)))) + 1));
                add 13, 8 => (to_integer(count(item(pool, _))) + at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) +
                    at(function.entry, to_integer(pool->capacity)) + to_integer(count(slot(pool))) +
                    to_integer(old(count(item(pool, _))))) < ((to_integer(old(count(item(pool, _))))
                    - 1) + at(function.entry, to_integer(pool->capacity)) + at(function.entry,
                    (to_integer((pool->checked_out - 1)) + to_integer((old(count(slot(pool))) +
                    1)))) + (to_integer(old(count(slot(pool)))) + 1) +
                    to_integer(old(pool->checked_out)));
                add 14, 10 => (to_integer(count(item(pool, _))) + at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) +
                    at(function.entry, to_integer(pool->capacity)) + to_integer(count(slot(pool))) +
                    to_integer(old(count(item(pool, _)))) + to_integer(pool->checked_out)) <
                    ((to_integer(old(count(item(pool, _)))) - 1) + at(function.entry,
                    to_integer(pool->capacity)) + at(function.entry, (to_integer((pool->checked_out
                    - 1)) + to_integer((old(count(slot(pool))) + 1)))) +
                    (to_integer(old(count(slot(pool)))) + 1) + to_integer(old(pool->checked_out)) +
                    to_integer(count(item(pool, _))));
                conclusion 15;
            }
        }
        arithmetic_certificate {
            premise 0: to_integer(count(item(pool, _))) <= (to_integer(old(count(item(pool, _)))) -
                1) => to_integer(count(item(pool, _))) <= (to_integer(old(count(item(pool, _)))) -
                1);
            premise 1: (to_integer(old(count(item(pool, _)))) - 1) <= to_integer(count(item(pool,
                _))) => (to_integer(old(count(item(pool, _)))) - 1) <= to_integer(count(item(pool,
                _)));
            equal_from_bounds 0, 1 => to_integer(count(item(pool, _))) ==
                (to_integer(old(count(item(pool, _)))) - 1);
            conclusion 2;
        }
    }
    have to_integer(pool->checked_out) == (to_integer(old(pool->checked_out)) - 1) by {
        assumption();
    }
    have defined((pool->checked_out + count(slot(pool)))) by {
        have (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) >= -2147483648 by {
            arithmetic_certificate {
                negated_goal => (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) <
                    -2147483648;
                premise 0: at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool))))) =>
                    at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer(pool->checked_out) + to_integer(count(slot(pool)))));
                less_equal_from_equal 1 reverse => at(function.entry, (to_integer(pool->checked_out)
                    + to_integer(count(slot(pool))))) <= at(function.entry,
                    to_integer(pool->capacity));
                premise 1: at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer((pool->checked_out - 1)) + to_integer((old(count(slot(pool))) +
                    1)))) => at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer((pool->checked_out - 1)) + to_integer((old(count(slot(pool))) +
                    1))));
                less_equal_from_equal 3 => at(function.entry, to_integer(pool->capacity)) <=
                    at(function.entry, (to_integer((pool->checked_out - 1)) +
                    to_integer((old(count(slot(pool))) + 1))));
                premise 2: to_integer(pool->checked_out) == (to_integer(old(pool->checked_out)) - 1)
                    => to_integer(pool->checked_out) == (to_integer(old(pool->checked_out)) - 1);
                less_equal_from_equal 5 => to_integer(pool->checked_out) <=
                    (to_integer(old(pool->checked_out)) - 1);
                premise 3: 0 <= to_integer(pool->checked_out) => 0 <= to_integer(pool->checked_out);
                premise 4: (to_integer(old(count(slot(pool)))) + 1) >= -2147483648 =>
                    (to_integer(old(count(slot(pool)))) + 1) >= -2147483648;
                add 0, 2 => (to_integer(pool->checked_out) + to_integer(count(slot(pool))) +
                    at(function.entry, (to_integer(pool->checked_out) +
                    to_integer(count(slot(pool)))))) < (-2147483648 + at(function.entry,
                    to_integer(pool->capacity)));
                add 9, 4 => (to_integer(pool->checked_out) + to_integer(count(slot(pool))) +
                    at(function.entry, (to_integer(pool->checked_out) +
                    to_integer(count(slot(pool))))) + at(function.entry,
                    to_integer(pool->capacity))) < (-2147483648 + at(function.entry,
                    to_integer(pool->capacity)) + at(function.entry, (to_integer((pool->checked_out
                    - 1)) + to_integer((old(count(slot(pool))) + 1)))));
                add 10, 6 => (to_integer(pool->checked_out) + to_integer(count(slot(pool))) +
                    at(function.entry, (to_integer(pool->checked_out) +
                    to_integer(count(slot(pool))))) + at(function.entry, to_integer(pool->capacity))
                    + to_integer(pool->checked_out)) < (-2147483648 + at(function.entry,
                    to_integer(pool->capacity)) + at(function.entry, (to_integer((pool->checked_out
                    - 1)) + to_integer((old(count(slot(pool))) + 1)))) +
                    (to_integer(old(pool->checked_out)) - 1));
                add 11, 7 => (to_integer(pool->checked_out) + to_integer(count(slot(pool))) +
                    at(function.entry, (to_integer(pool->checked_out) +
                    to_integer(count(slot(pool))))) + at(function.entry, to_integer(pool->capacity))
                    + to_integer(pool->checked_out) + 0) < (-2147483648 + at(function.entry,
                    to_integer(pool->capacity)) + at(function.entry, (to_integer((pool->checked_out
                    - 1)) + to_integer((old(count(slot(pool))) + 1)))) +
                    (to_integer(old(pool->checked_out)) - 1) + to_integer(pool->checked_out));
                add 12, 8 => (to_integer(pool->checked_out) + to_integer(count(slot(pool))) +
                    at(function.entry, (to_integer(pool->checked_out) +
                    to_integer(count(slot(pool))))) + at(function.entry, to_integer(pool->capacity))
                    + to_integer(pool->checked_out) + 0 + -2147483648) < (-2147483648 +
                    at(function.entry, to_integer(pool->capacity)) + at(function.entry,
                    (to_integer((pool->checked_out - 1)) + to_integer((old(count(slot(pool))) +
                    1)))) + (to_integer(old(pool->checked_out)) - 1) + to_integer(pool->checked_out)
                    + (to_integer(old(count(slot(pool)))) + 1));
                conclusion 13;
            }
        }
        have (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) <= 2147483647 by {
            arithmetic_certificate {
                negated_goal => 2147483647 < (to_integer(pool->checked_out) +
                    to_integer(count(slot(pool))));
                premise 0: at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer((pool->checked_out - 1)) + to_integer((old(count(slot(pool))) +
                    1)))) => at(function.entry, to_integer(pool->capacity)) == at(function.entry,
                    (to_integer((pool->checked_out - 1)) + to_integer((old(count(slot(pool))) +
                    1))));
                less_equal_from_equal 1 reverse => at(function.entry, (to_integer((pool->checked_out
                    - 1)) + to_integer((old(count(slot(pool))) + 1)))) <= at(function.entry,
                    to_integer(pool->capacity));
                type_range => to_integer(at(function.entry, to_integer(pool->capacity))) <=
                    2147483647;
                add 0, 2 => (2147483647 + at(function.entry, (to_integer((pool->checked_out - 1)) +
                    to_integer((old(count(slot(pool))) + 1))))) < (to_integer(pool->checked_out) +
                    to_integer(count(slot(pool))) + at(function.entry, to_integer(pool->capacity)));
                add 4, 3 => (2147483647 + at(function.entry, (to_integer((pool->checked_out - 1)) +
                    to_integer((old(count(slot(pool))) + 1)))) + to_integer(at(function.entry,
                    to_integer(pool->capacity)))) < (to_integer(pool->checked_out) +
                    to_integer(count(slot(pool))) + at(function.entry, to_integer(pool->capacity)) +
                    2147483647);
                conclusion 5;
            }
        }
        assumption();
    }
    have to_integer(pool->capacity) == (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) by {
        assumption();
    }
    have 0 <= pool->checked_out and to_integer(pool->checked_out) == to_integer(count(item(pool, _))) and to_integer(pool->capacity) == (to_integer(pool->checked_out) + to_integer(count(slot(pool)))) by {
        assumption();
    }
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    normalize();
    assumption();
    assumption();
    assumption();
    normalize();
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
        assumption();
    }
    have defined((count(item(pool, _)) + 1)) by {
        have (to_integer(count(item(pool, _))) + to_integer(1)) >= -2147483648 by {
            arithmetic_certificate {
                negated_goal => (to_integer(count(item(pool, _))) + to_integer(1)) < -2147483648;
                premise 0: 0 <= to_integer(count(item(pool, _))) => 0 <= to_integer(count(item(pool,
                    _)));
                add 0, 1 => (to_integer(count(item(pool, _))) + to_integer(1) + 0) < (-2147483648 +
                    to_integer(count(item(pool, _))));
                conclusion 2;
            }
        }
        have (to_integer(count(item(pool, _))) + to_integer(1)) <= 2147483647 by {
            arithmetic_certificate {
                negated_goal => 2147483647 < (to_integer(count(item(pool, _))) + to_integer(1));
                premise 0: to_integer(count(item(pool, _))) == 0 => to_integer(count(item(pool, _)))
                    == 0;
                less_equal_from_equal 1 => to_integer(count(item(pool, _))) <= 0;
                add 0, 2 => (2147483647 + to_integer(count(item(pool, _)))) <
                    (to_integer(count(item(pool, _))) + to_integer(1) + 0);
                conclusion 3;
            }
        }
        assumption();
    }
    step();
    have to_integer(count(item(pool, _))) == 1 by {
        assumption();
    }
    have defined((count(item(pool, _)) + 1)) by {
        have (to_integer(count(item(pool, _))) + to_integer(1)) >= -2147483648 by {
            arithmetic_certificate {
                negated_goal => (to_integer(count(item(pool, _))) + to_integer(1)) < -2147483648;
                premise 0: to_integer(count(item(pool, _))) == 1 => to_integer(count(item(pool, _)))
                    == 1;
                less_equal_from_equal 1 reverse => 1 <= to_integer(count(item(pool, _)));
                add 0, 2 => (to_integer(count(item(pool, _))) + to_integer(1) + 1) < (-2147483648 +
                    to_integer(count(item(pool, _))));
                conclusion 3;
            }
        }
        have (to_integer(count(item(pool, _))) + to_integer(1)) <= 2147483647 by {
            arithmetic_certificate {
                negated_goal => 2147483647 < (to_integer(count(item(pool, _))) + to_integer(1));
                premise 0: to_integer(count(item(pool, _))) == 1 => to_integer(count(item(pool, _)))
                    == 1;
                less_equal_from_equal 1 => to_integer(count(item(pool, _))) <= 1;
                add 0, 2 => (2147483647 + to_integer(count(item(pool, _)))) <
                    (to_integer(count(item(pool, _))) + to_integer(1) + 1);
                conclusion 3;
            }
        }
        assumption();
    }
    step();
    open(item(pool, first)) {
        step();
    }
    open(item(pool, second)) {
        step();
    }
    have to_integer(count(item(pool, second))) == 1 by {
        normalize();
    }
    step();
    have to_integer(count(item(pool, first))) == 1 by {
        normalize();
    }
    step();
    step();
    assumption();
    have pool->checked_out == 0 by {
        assumption();
    }
    have pool->capacity == 2 by {
        assumption();
    }
    have first->value == 11 by {
        assumption();
    }
    have second->value == 22 by {
        assumption();
    }
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
}
```

```expect
pass
```
