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

```click resource_semantics=authority
authorized resource slot(pool: struct pool*) {}
authorized resource item(pool: struct pool*, p: struct payload*) { owns object(p); }
resource storage(pool: struct pool*) {
    owns object(pool);
    owns authority(slot(pool));
    owns authority(item(pool, _));
}
resource control(pool: struct pool*) {
    owns object(pool);
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
    step(); step();
    fold(amount of slot(pool));
    fold(control(pool));
    execute(); unfold(valid_pool); simp();
}
void checkout(struct pool* pool, struct payload* p) {
    owns control(pool);
    requires pool->checked_out < 2147483647;
    consumes slot(pool);
    consumes object(p);
    produces item(pool, p);
    ensures count(slot(pool)) == old(count(slot(pool))) - 1;
    ensures count(item(pool, _)) == old(count(item(pool, _))) + 1;
    ensures pool->checked_out == old(pool->checked_out) + 1;
    ensures pool->capacity == old(pool->capacity);
} by {
    open(control(pool)) {
        have 1 <= count(slot(pool)) by simp;
        apply(int32_move_one_from_right_to_left_preserves_sum(
            pool->capacity, pool->checked_out, count(slot(pool))
        )) using {
            0 <= pool->checked_out;
            1 <= count(slot(pool));
            pool->capacity == pool->checked_out + count(slot(pool));
        }
        unfold(slot(pool));
        step();
        fold(item(pool, p));
        have pool->capacity == pool->checked_out + count(slot(pool)) by simp;
    }
    execute(); simp();
}
void give_back(struct pool* pool, struct payload* p) {
    owns control(pool);
    requires count(item(pool, p)) == 1;
    consumes item(pool, p);
    produces object(p);
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
        have 1 <= count(item(pool, _)) by simp;
        have 1 <= pool->checked_out by {
            rewrite(pool->checked_out == count(item(pool, _)));
            assumption();
        }
        have pool->capacity == count(slot(pool)) + pool->checked_out by simp;
        apply(int32_move_one_from_right_to_left_preserves_sum(
            pool->capacity, count(slot(pool)), pool->checked_out
        )) using {
            0 <= count(slot(pool));
            1 <= pool->checked_out;
            pool->capacity == count(slot(pool)) + pool->checked_out;
        }
        have 0 < pool->checked_out by simp;
        have 0 < pool->checked_out by simp;
        have defined(pool->checked_out + count(slot(pool))) by simp;
        apply(int32_add_to_integer(pool->checked_out, count(slot(pool)))) using {
            defined(pool->checked_out + count(slot(pool)));
        }
        have to_integer(pool->capacity) == to_integer(pool->checked_out) + to_integer(count(slot(pool))) by {
            rewrite(pool->capacity == pool->checked_out + count(slot(pool)));
            assumption();
        }
        have pool->capacity <= 2147483647 by simp;
        have to_integer(pool->capacity) <= 2147483647 by {
            apply(int32_less_equal_to_integer(pool->capacity, 2147483647)) using { pool->capacity <= 2147483647; }
            simp();
        }
        have 1 <= to_integer(pool->checked_out) by {
            apply(int32_less_equal_to_integer(1, pool->checked_out)) using { 1 <= pool->checked_out; }
            simp();
        }
        have to_integer(count(slot(pool))) + 1 <= 2147483647 by {
            arithmetic_certificate {
                premise 0: to_integer(pool->capacity) == to_integer(pool->checked_out) + to_integer(count(slot(pool))) => to_integer(pool->capacity) == to_integer(pool->checked_out) + to_integer(count(slot(pool)));
                scale 0 by -1 => -to_integer(pool->capacity) == -to_integer(pool->checked_out) - to_integer(count(slot(pool)));
                eq_to_le 1 => -to_integer(pool->capacity) <= -to_integer(pool->checked_out) - to_integer(count(slot(pool)));
                premise 1: to_integer(pool->capacity) <= 2147483647 => to_integer(pool->capacity) <= 2147483647;
                add 2, 3 => -to_integer(pool->capacity) + to_integer(pool->capacity) <= -to_integer(pool->checked_out) - to_integer(count(slot(pool))) + 2147483647;
                premise 2: 1 <= to_integer(pool->checked_out) => 1 <= to_integer(pool->checked_out);
                add 4, 5 => -to_integer(pool->capacity) + to_integer(pool->capacity) + 1 <= -to_integer(pool->checked_out) - to_integer(count(slot(pool))) + 2147483647 + to_integer(pool->checked_out);
                conclusion 6;
            }
        }
        have 0 <= to_integer(count(slot(pool))) by {
            apply(int32_less_equal_to_integer(0, count(slot(pool)))) using { 0 <= count(slot(pool)); }
            simp();
        }
        have to_integer(count(slot(pool))) + 1 >= -2147483648 by {
            arithmetic() using { 0 <= to_integer(count(slot(pool))); }
        }
        have defined(count(slot(pool)) + 1) by {
            apply(int32_add_defined_by_integer_bounds(count(slot(pool)), 1)) using {
                to_integer(count(slot(pool))) + 1 >= -2147483648;
                to_integer(count(slot(pool))) + 1 <= 2147483647;
            }
            simp();
        }
        unfold(item(pool, p));
        step();
        fold(slot(pool));
        have pool->capacity == old(pool->capacity) by simp;
        have pool->checked_out == old(pool->checked_out) - 1 by simp;
        have count(slot(pool)) == old(count(slot(pool))) + 1 by simp;
        have 0 <= pool->checked_out by {
            rewrite(pool->checked_out == old(pool->checked_out) - 1);
            apply(int32_positive_predecessor_is_nonnegative(old(pool->checked_out))) using { 0 < old(pool->checked_out); }
            assumption();
        }
        have pool->checked_out == count(item(pool, _)) by simp;
        have 0 <= pool->checked_out by {
            rewrite(pool->checked_out == old(pool->checked_out) - 1);
            apply(int32_positive_predecessor_is_nonnegative(old(pool->checked_out))) using { 0 < old(pool->checked_out); }
            assumption();
        }
        have pool->checked_out == count(item(pool, _)) by simp;
        have pool->capacity == pool->checked_out + count(slot(pool)) by {
            rewrite(pool->capacity == old(pool->capacity));
            rewrite(pool->checked_out == old(pool->checked_out) - 1);
            rewrite(count(slot(pool)) == old(count(slot(pool))) + 1);
            rewrite(old(pool->capacity) == (old(count(slot(pool))) + 1) + (old(pool->checked_out) - 1));
            normalize();
        }
    }
    execute(); unfold(valid_pool); simp();
}
void pipeline(struct pool* pool, struct payload* first, struct payload* second) {
 consumes storage(pool);
 requires count(slot(pool)) == 0;
 requires count(item(pool, _)) == 0;
 owns object(first); owns object(second);
 produces control(pool);
 produces 2 of slot(pool);
 ensures pool->checked_out == 0;
 ensures pool->capacity == 2;
 ensures first->value == 11;
 ensures second->value == 22;
} by {
 step();
 have count(item(pool, _)) == 0 by simp;
 have defined(count(item(pool, _)) + 1) by simp;
 step();
 have count(item(pool, _)) == 1 by simp;
 have defined(count(item(pool, _)) + 1) by simp;
 step();
 open(item(pool, first)) { step(); }
 open(item(pool, second)) { step(); }
 have count(item(pool, second)) == 1 by simp;
 step();
 have count(item(pool, first)) == 1 by simp;
 step();
 execute(); simp();
}
```

```expect
pass
```
