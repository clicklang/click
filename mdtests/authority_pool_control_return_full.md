# Pool control preserves both population invariants through return

```c filename=pool_control.c
struct pool { int32 checked_out; int32 capacity; };
struct payload { int32 value; };
void give_back(struct pool* pool, struct payload* p) {
    pool->checked_out = pool->checked_out - 1;
}
void forward(struct pool* pool, struct payload* p) { give_back(pool, p); }
void caller(struct pool* pool, struct payload* p) { forward(pool, p); }
```

```click resource_semantics=authority
resource slot(pool: struct pool*) {}
resource item(pool: struct pool*, p: struct payload*) { owns object(p); }
resource control(pool: struct pool*) {
    owns object(pool);
    owns authority(slot(pool));
    owns authority(item(pool, _));
    fact 0 <= pool->checked_out;
    fact pool->checked_out == count(item(pool, _));
    fact pool->capacity == pool->checked_out + count(slot(pool));
}
theorem slot_increment_defined(capacity: int32, used: int32, slots: int32) {
    requires 1 <= used;
    requires 0 <= slots;
    requires capacity == used + slots;
    requires defined(used + slots);
    ensures defined(slots + 1) by {
    have defined(used + slots) by simp;
    apply(int32_add_to_integer(used, slots)) using {
        defined(used + slots);
    }
    have to_integer(capacity) == to_integer(used) + to_integer(slots) by {
        rewrite(capacity == used + slots);
        assumption();
    }
    have capacity <= 2147483647 by simp;
    have to_integer(capacity) <= 2147483647 by {
        apply(int32_less_equal_to_integer(capacity, 2147483647)) using { capacity <= 2147483647; }
        simp();
    }
    have 1 <= to_integer(used) by {
        apply(int32_less_equal_to_integer(1, used)) using { 1 <= used; }
        simp();
    }
    have to_integer(slots) + 1 <= 2147483647 by {
        arithmetic_certificate {
        premise 0: to_integer(capacity) == to_integer(used) + to_integer(slots) => to_integer(capacity) == to_integer(used) + to_integer(slots);
        scale 0 by -1 => -to_integer(capacity) == -to_integer(used) - to_integer(slots);
        eq_to_le 1 => -to_integer(capacity) <= -to_integer(used) - to_integer(slots);
        premise 1: to_integer(capacity) <= 2147483647 => to_integer(capacity) <= 2147483647;
        add 2, 3 => -to_integer(capacity) + to_integer(capacity) <= -to_integer(used) - to_integer(slots) + 2147483647;
        premise 2: 1 <= to_integer(used) => 1 <= to_integer(used);
        add 4, 5 => -to_integer(capacity) + to_integer(capacity) + 1 <= -to_integer(used) - to_integer(slots) + 2147483647 + to_integer(used);
        conclusion 6;
        }
    }
    have 0 <= to_integer(slots) by {
        apply(int32_less_equal_to_integer(0, slots)) using { 0 <= slots; }
        simp();
    }
    have to_integer(slots) + 1 >= -2147483648 by {
        arithmetic() using { 0 <= to_integer(slots); }
    }
    have defined(slots + 1) by {
        apply(int32_add_defined_by_integer_bounds(slots, 1)) using {
        to_integer(slots) + 1 >= -2147483648;
        to_integer(slots) + 1 <= 2147483647;
        }
        simp();
    }
    assumption();
    }
}
predicate valid_pool(pool: struct pool*) {
    0 <= pool->checked_out and
    pool->checked_out == count(item(pool, _)) and
    pool->capacity == pool->checked_out + count(slot(pool))
}
verifying "pool_control.c";
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
void forward(struct pool* pool, struct payload* p) {
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
} by {
    open(control(pool)) {
        have 1 <= count(item(pool, _)) by simp;
        have 1 <= pool->checked_out by {
            rewrite(pool->checked_out == count(item(pool, _))); assumption();
        }
        have defined(pool->checked_out + count(slot(pool))) by simp;
        have 0 <= count(slot(pool)) by simp;
        apply(slot_increment_defined(pool->capacity, pool->checked_out, count(slot(pool)))) using {
            1 <= pool->checked_out;
            0 <= count(slot(pool));
            pool->capacity == pool->checked_out + count(slot(pool));
            defined(pool->checked_out + count(slot(pool)));
        }
    }
    execute(); unfold(valid_pool); simp();
}
void caller(struct pool* pool, struct payload* p) {
    owns control(pool);
    requires count(item(pool, p)) == 1;
    owns slot(pool);
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
} by {
    open(control(pool)) {
        have 1 <= count(item(pool, _)) by simp;
        have 1 <= pool->checked_out by {
            rewrite(pool->checked_out == count(item(pool, _))); assumption();
        }
        have defined(pool->checked_out + count(slot(pool))) by simp;
        have 1 <= count(slot(pool)) by simp;
        have 0 <= count(slot(pool)) by {
            apply(int32_positive_is_nonnegative(count(slot(pool)))) using { 1 <= count(slot(pool)); }
            assumption();
        }
        apply(slot_increment_defined(pool->capacity, pool->checked_out, count(slot(pool)))) using {
            1 <= pool->checked_out;
            0 <= count(slot(pool));
            pool->capacity == pool->checked_out + count(slot(pool));
            defined(pool->checked_out + count(slot(pool)));
        }
    }
    execute(); unfold(valid_pool); simp();
}
```

```expect
pass
```
