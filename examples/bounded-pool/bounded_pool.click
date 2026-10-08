authorized resource pool_slot(pool: struct pool*) {}
authorized resource pool_object(pool: struct pool*, object: struct object*) { owns *object; }
resource pool_storage(pool: struct pool*) {
    owns *pool;
    owns authority(pool_slot(pool));
    owns authority(pool_object(pool, _));
}
resource pool_control(pool: struct pool*) {
    owns *pool;
    owns authority(pool_slot(pool));
    owns authority(pool_object(pool, _));
    fact 0 <= pool->checked_out;
    fact pool->checked_out == count(pool_object(pool, _));
    fact pool->capacity == pool->checked_out + count(pool_slot(pool));
}
theorem pool_checkout_increment_bound(capacity: int32, used: int32, available: int32) {
    requires 0 <= used;
    requires 1 <= available;
    requires capacity == used + available;
    requires defined(used + available);
    ensures to_integer(used) + 1 <= 2147483647 by {
        apply(int32_add_to_integer(used, available)) using { defined(used + available); }
        have to_integer(capacity) == to_integer(used) + to_integer(available) by {
            rewrite(capacity == used + available);
            simp();
        }
        have capacity <= 2147483647 by simp;
        have to_integer(capacity) <= 2147483647 by {
            apply(int32_less_equal_to_integer(capacity, 2147483647)) using { capacity <= 2147483647; }
            simp();
        }
        have 1 <= to_integer(available) by {
            apply(int32_less_equal_to_integer(1, available)) using { 1 <= available; }
            simp();
        }
        arithmetic_certificate {
            premise 0: to_integer(capacity) == to_integer(used) + to_integer(available) => to_integer(capacity) == to_integer(used) + to_integer(available);
            scale 0 by -1 => -to_integer(capacity) == -to_integer(available) - to_integer(used);
            eq_to_le 1 => -to_integer(capacity) <= -to_integer(available) - to_integer(used);
            premise 1: to_integer(capacity) <= 2147483647 => to_integer(capacity) <= 2147483647;
            add 2, 3 => -to_integer(capacity) + to_integer(capacity) <= -to_integer(available) - to_integer(used) + 2147483647;
            premise 2: 1 <= to_integer(available) => 1 <= to_integer(available);
            add 4, 5 => -to_integer(capacity) + to_integer(capacity) + 1 <= -to_integer(available) - to_integer(used) + 2147483647 + to_integer(available);
            conclusion 6;
        }
    }
}
theorem pool_shrink_sum_defined(capacity: int32, used: int32, available: int32, amount: int32) {
    requires 0 <= used;
    requires 0 <= amount;
    requires amount <= available;
    requires capacity == used + available;
    requires defined(used + available);
    ensures defined(used + (available - amount)) by {
        apply(int32_nonnegative_subtract_within_value_is_defined(available, amount)) using {
            0 <= amount; amount <= available;
        }
        have defined(available - amount) by simp;
        have 0 <= available - amount by {
            arithmetic() using { 0 <= amount; amount <= available; }
        }
        apply(int32_add_to_integer(used, available)) using { defined(used + available); }
        have to_integer(capacity) == to_integer(used) + to_integer(available) by {
            rewrite(capacity == used + available); simp();
        }
        apply(int32_subtract_to_integer(available, amount)) using { defined(available - amount); }
        have capacity <= 2147483647 by simp;
        have to_integer(capacity) <= 2147483647 by {
            apply(int32_less_equal_to_integer(capacity, 2147483647)) using { capacity <= 2147483647; }
            simp();
        }
        have 0 <= to_integer(amount) by {
            apply(int32_less_equal_to_integer(0, amount)) using { 0 <= amount; }
            simp();
        }
        have to_integer(used) + to_integer(available - amount) <= 2147483647 by {
            arithmetic_certificate {
                premise 0: to_integer(capacity) == to_integer(used) + to_integer(available) => to_integer(capacity) == to_integer(used) + to_integer(available);
                scale 0 by -1 => -to_integer(capacity) == -to_integer(used) - to_integer(available);
                eq_to_le 1 => -to_integer(capacity) <= -to_integer(used) - to_integer(available);
                premise 1: to_integer(available - amount) == to_integer(available) - to_integer(amount) => to_integer(available - amount) == to_integer(available) - to_integer(amount);
                eq_to_le 3 => to_integer(available - amount) <= to_integer(available) - to_integer(amount);
                premise 2: to_integer(capacity) <= 2147483647 => to_integer(capacity) <= 2147483647;
                add 2, 5 => -to_integer(capacity) + to_integer(capacity) <= -to_integer(used) - to_integer(available) + 2147483647;
                add 6, 4 => -to_integer(capacity) + to_integer(capacity) + to_integer(available - amount) <= -to_integer(used) - to_integer(available) + 2147483647 + to_integer(available) - to_integer(amount);
                premise 3: 0 <= to_integer(amount) => 0 <= to_integer(amount);
                add 7, 8 => -to_integer(capacity) + to_integer(capacity) + to_integer(available - amount) + 0 <= -to_integer(used) - to_integer(available) + 2147483647 + to_integer(available) - to_integer(amount) + to_integer(amount);
                conclusion 9;
            }
        }
        have 0 <= to_integer(used) by {
            apply(int32_less_equal_to_integer(0, used)) using { 0 <= used; }
            simp();
        }
        have 0 <= to_integer(available - amount) by {
            apply(int32_less_equal_to_integer(0, available - amount)) using { 0 <= available - amount; }
            simp();
        }
        have to_integer(used) + to_integer(available - amount) >= -2147483648 by {
            arithmetic() using { 0 <= to_integer(used); 0 <= to_integer(available - amount); }
        }
        apply(int32_add_defined_by_integer_bounds(used, available - amount)) using {
            to_integer(used) + to_integer(available - amount) >= -2147483648;
            to_integer(used) + to_integer(available - amount) <= 2147483647;
        }
        simp();
    }
}
theorem pool_shrink_conservation(capacity: int32, used: int32, available: int32, amount: int32) {
    requires 0 <= used;
    requires 0 <= amount;
    requires amount <= available;
    requires capacity == used + available;
    requires defined(used + available);
    requires defined(capacity - amount);
    ensures capacity - amount == used + (available - amount) by {
        apply(pool_shrink_sum_defined(capacity, used, available, amount)) using {
            0 <= used; 0 <= amount; amount <= available;
            capacity == used + available; defined(used + available);
        }
        have defined(used + (available - amount)) by simp;
        apply(int32_nonnegative_subtract_within_value_is_defined(available, amount)) using {
            0 <= amount; amount <= available;
        }
        have defined(available - amount) by simp;
        apply(int32_add_to_integer(used, available)) using { defined(used + available); }
        have to_integer(capacity) == to_integer(used) + to_integer(available) by {
            rewrite(capacity == used + available); assumption();
        }
        apply(int32_subtract_to_integer(capacity, amount)) using { defined(capacity - amount); }
        apply(int32_subtract_to_integer(available, amount)) using { defined(available - amount); }
        apply(int32_add_to_integer(used, available - amount)) using { defined(used + (available - amount)); }
        have to_integer(capacity - amount) == to_integer(used + (available - amount)) by {
            arithmetic_certificate {
                premise 0: to_integer(capacity - amount) == to_integer(capacity) - to_integer(amount) => to_integer(capacity - amount) == to_integer(capacity) - to_integer(amount);
                premise 1: to_integer(capacity) == to_integer(used) + to_integer(available) => to_integer(capacity) == to_integer(used) + to_integer(available);
                add 0, 1 => to_integer(capacity - amount) == to_integer(used) + to_integer(available) - to_integer(amount);
                premise 2: to_integer(available - amount) == to_integer(available) - to_integer(amount) => to_integer(available - amount) == to_integer(available) - to_integer(amount);
                scale 3 by -1 => to_integer(available) - to_integer(amount) == to_integer(available - amount);
                add 2, 4 => to_integer(capacity - amount) == to_integer(used) + to_integer(available - amount);
                premise 3: to_integer(used + (available - amount)) == to_integer(used) + to_integer(available - amount) => to_integer(used + (available - amount)) == to_integer(used) + to_integer(available - amount);
                scale 6 by -1 => to_integer(used) + to_integer(available - amount) == to_integer(used + (available - amount));
                add 5, 7 => to_integer(capacity - amount) == to_integer(used + (available - amount));
                conclusion 8;
            }
        }
        apply(int32_equal_of_to_integer(capacity - amount, used + (available - amount))) using {
            to_integer(capacity - amount) == to_integer(used + (available - amount));
        }
        assumption();
    }
}
theorem pool_grow_slots_defined(capacity: int32, used: int32, available: int32, amount: int32) {
    requires 0 <= used;
    requires 0 <= available;
    requires 0 <= amount;
    requires capacity == used + available;
    requires defined(used + available);
    requires defined(capacity + amount);
    ensures defined(available + amount) by {
        apply(int32_add_to_integer(used, available)) using { defined(used + available); }
        have to_integer(capacity) == to_integer(used) + to_integer(available) by {
            rewrite(capacity == used + available); assumption();
        }
        apply(int32_add_to_integer(capacity, amount)) using { defined(capacity + amount); }
        have capacity + amount <= 2147483647 by simp;
        have to_integer(capacity + amount) <= 2147483647 by {
            apply(int32_less_equal_to_integer(capacity + amount, 2147483647)) using { capacity + amount <= 2147483647; }
            simp();
        }
        have 0 <= to_integer(used) by {
            apply(int32_less_equal_to_integer(0, used)) using { 0 <= used; } simp();
        }
        have to_integer(available) + to_integer(amount) <= 2147483647 by {
            arithmetic_certificate {
                premise 0: to_integer(capacity) == to_integer(used) + to_integer(available) => to_integer(capacity) == to_integer(used) + to_integer(available);
                scale 0 by -1 => -to_integer(capacity) == -to_integer(used) - to_integer(available);
                eq_to_le 1 => -to_integer(capacity) <= -to_integer(used) - to_integer(available);
                premise 1: to_integer(capacity + amount) == to_integer(capacity) + to_integer(amount) => to_integer(capacity + amount) == to_integer(capacity) + to_integer(amount);
                scale 3 by -1 => -to_integer(capacity + amount) == -to_integer(capacity) - to_integer(amount);
                eq_to_le 4 => -to_integer(capacity + amount) <= -to_integer(capacity) - to_integer(amount);
                add 2, 5 => -to_integer(capacity + amount) <= -to_integer(used) - to_integer(available) - to_integer(amount);
                premise 2: to_integer(capacity + amount) <= 2147483647 => to_integer(capacity + amount) <= 2147483647;
                add 6, 7 => 0 <= 2147483647 - to_integer(used) - to_integer(available) - to_integer(amount);
                premise 3: 0 <= to_integer(used) => 0 <= to_integer(used);
                add 8, 9 => 0 <= 2147483647 - to_integer(available) - to_integer(amount);
                conclusion 10;
            }
        }
        have 0 <= to_integer(available) by {
            apply(int32_less_equal_to_integer(0, available)) using { 0 <= available; } simp();
        }
        have 0 <= to_integer(amount) by {
            apply(int32_less_equal_to_integer(0, amount)) using { 0 <= amount; } simp();
        }
        have to_integer(available) + to_integer(amount) >= -2147483648 by {
            arithmetic() using { 0 <= to_integer(available); 0 <= to_integer(amount); }
        }
        apply(int32_add_defined_by_integer_bounds(available, amount)) using {
            to_integer(available) + to_integer(amount) >= -2147483648;
            to_integer(available) + to_integer(amount) <= 2147483647;
        }
        simp();
    }
}
theorem pool_grow_conservation(capacity: int32, used: int32, available: int32, amount: int32) {
    requires 0 <= used;
    requires 0 <= available;
    requires 0 <= amount;
    requires capacity == used + available;
    requires defined(used + available);
    requires defined(capacity + amount);
    ensures defined(used + (available + amount)) and
        capacity + amount == used + (available + amount) by {
        apply(pool_grow_slots_defined(capacity, used, available, amount)) using {
            0 <= used; 0 <= available; 0 <= amount;
            capacity == used + available; defined(used + available); defined(capacity + amount);
        }
        have defined(available + amount) by simp;
        apply(int32_add_to_integer(used, available)) using { defined(used + available); }
        have to_integer(capacity) == to_integer(used) + to_integer(available) by {
            rewrite(capacity == used + available); assumption();
        }
        apply(int32_add_to_integer(capacity, amount)) using { defined(capacity + amount); }
        apply(int32_add_to_integer(available, amount)) using { defined(available + amount); }
        have to_integer(used) + to_integer(available + amount) == to_integer(capacity + amount) by {
            arithmetic_certificate {
                premise 0: to_integer(capacity) == to_integer(used) + to_integer(available) => to_integer(capacity) == to_integer(used) + to_integer(available);
                premise 1: to_integer(capacity + amount) == to_integer(capacity) + to_integer(amount) => to_integer(capacity + amount) == to_integer(capacity) + to_integer(amount);
                add 0, 1 => to_integer(capacity + amount) == to_integer(used) + to_integer(available) + to_integer(amount);
                premise 2: to_integer(available + amount) == to_integer(available) + to_integer(amount) => to_integer(available + amount) == to_integer(available) + to_integer(amount);
                scale 3 by -1 => to_integer(available) + to_integer(amount) == to_integer(available + amount);
                add 2, 4 => to_integer(capacity + amount) == to_integer(used) + to_integer(available + amount);
                scale 5 by -1 => to_integer(used) + to_integer(available + amount) == to_integer(capacity + amount);
                conclusion 6;
            }
        }
        have capacity + amount <= 2147483647 by simp;
        have -2147483648 <= capacity + amount by simp;
        have to_integer(capacity + amount) <= 2147483647 by {
            apply(int32_less_equal_to_integer(capacity + amount, 2147483647)) using { capacity + amount <= 2147483647; } simp();
        }
        have -2147483648 <= to_integer(capacity + amount) by {
            apply(int32_less_equal_to_integer(-2147483648, capacity + amount)) using { -2147483648 <= capacity + amount; } simp();
        }
        have to_integer(used) + to_integer(available + amount) >= -2147483648 by {
            arithmetic_certificate {
                premise 0: to_integer(used) + to_integer(available + amount) == to_integer(capacity + amount) => to_integer(used) + to_integer(available + amount) == to_integer(capacity + amount);
                scale 0 by -1 => to_integer(capacity + amount) == to_integer(used) + to_integer(available + amount);
                eq_to_le 1 => to_integer(capacity + amount) <= to_integer(used) + to_integer(available + amount);
                premise 1: -2147483648 <= to_integer(capacity + amount) => -2147483648 <= to_integer(capacity + amount);
                add 2, 3 => -2147483648 <= to_integer(used) + to_integer(available + amount);
                conclusion 4;
            }
        }
        have to_integer(used) + to_integer(available + amount) <= 2147483647 by {
            arithmetic_certificate {
                premise 0: to_integer(used) + to_integer(available + amount) == to_integer(capacity + amount) => to_integer(used) + to_integer(available + amount) == to_integer(capacity + amount);
                eq_to_le 0 => to_integer(used) + to_integer(available + amount) <= to_integer(capacity + amount);
                premise 1: to_integer(capacity + amount) <= 2147483647 => to_integer(capacity + amount) <= 2147483647;
                add 1, 2 => to_integer(used) + to_integer(available + amount) <= 2147483647;
                conclusion 3;
            }
        }
        apply(int32_add_defined_by_integer_bounds(used, available + amount)) using {
            to_integer(used) + to_integer(available + amount) >= -2147483648;
            to_integer(used) + to_integer(available + amount) <= 2147483647;
        }
        have defined(used + (available + amount)) by simp;
        apply(int32_add_to_integer(used, available + amount)) using { defined(used + (available + amount)); }
        have to_integer(capacity + amount) == to_integer(used + (available + amount)) by {
            arithmetic_certificate {
                premise 0: to_integer(used) + to_integer(available + amount) == to_integer(capacity + amount) => to_integer(used) + to_integer(available + amount) == to_integer(capacity + amount);
                scale 0 by -1 => to_integer(capacity + amount) == to_integer(used) + to_integer(available + amount);
                premise 1: to_integer(used + (available + amount)) == to_integer(used) + to_integer(available + amount) => to_integer(used + (available + amount)) == to_integer(used) + to_integer(available + amount);
                scale 2 by -1 => to_integer(used) + to_integer(available + amount) == to_integer(used + (available + amount));
                add 1, 3 => to_integer(capacity + amount) == to_integer(used + (available + amount));
                conclusion 4;
            }
        }
        apply(int32_equal_of_to_integer(capacity + amount, used + (available + amount))) using {
            to_integer(capacity + amount) == to_integer(used + (available + amount));
        }
        assumption();
    }
}
predicate valid_pool(pool: struct pool*) {
    0 <= pool->checked_out and
    pool->checked_out == count(pool_object(pool, _)) and
    pool->capacity == pool->checked_out + count(pool_slot(pool))
}
verifying "pool_init.c";
verifying "pool_destroy.c";
verifying "pool_zero_pipeline.c";
verifying "pool_checkout.c";
verifying "pool_return.c";
verifying "pool_transfer.c";
verifying "pool_transfer_pipeline.c";
verifying "pool_pipeline.c";
verifying "pool_grow.c";
verifying "pool_shrink.c";
verifying "pool_resize_pipeline.c";
void pool_init(struct pool* pool, int32 capacity) {
    consumes pool_storage(pool);
    requires 0 <= capacity;
    requires count(pool_slot(pool)) == 0;
    requires count(pool_object(pool, _)) == 0;
    produces pool_control(pool);
    produces capacity of pool_slot(pool);
    ensures pool->capacity == capacity;
    ensures pool->checked_out == 0;
    ensures count(pool_object(pool, _)) == 0;
    ensures valid_pool(pool);
} by {
    unfold(pool_storage(pool));
    step(); step();
    fold(capacity of pool_slot(pool));
    fold(pool_control(pool));
    execute(); unfold(valid_pool); simp();
}
void pool_destroy(struct pool* pool) {
    consumes pool_control(pool);
    consumes pool->capacity of pool_slot(pool);
    requires pool->checked_out == 0;
    produces *pool;
    ensures pool->checked_out == 0;
    ensures pool->capacity == 0;
    ensures count(pool_slot(pool)) == 0;
    ensures count(pool_object(pool, _)) == 0;
    ensures valid_pool(pool);
} by {
    unfold(pool_control(pool));
    have count(pool_object(pool, _)) == 0 by simp;
    have pool->capacity == count(pool_slot(pool)) by simp;
    unfold(pool->capacity of pool_slot(pool));
    have count(pool_slot(pool)) == 0 by simp;
    step();
    unfold(authority(pool_slot(pool)));
    unfold(authority(pool_object(pool, _)));
    execute(); unfold(valid_pool); simp();
}
void pool_zero_pipeline(struct pool* pool) {
    consumes pool_storage(pool);
    requires count(pool_slot(pool)) == 0;
    requires count(pool_object(pool, _)) == 0;
    produces *pool;
    ensures pool->checked_out == 0;
    ensures pool->capacity == 0;
    ensures count(pool_slot(pool)) == 0;
    ensures count(pool_object(pool, _)) == 0;
    ensures valid_pool(pool);
} by {
    step();
    unfold(pool_control(pool));
    have pool->capacity == count(pool_slot(pool)) by simp;
    have count(pool_object(pool, _)) == 0 by simp;
    fold(pool_control(pool));
    step();
    execute(); unfold(valid_pool); simp();
}

void pool_checkout(struct pool* pool, struct object* object) {
    owns pool_control(pool);
    consumes pool_slot(pool);
    consumes *object;
    produces pool_object(pool, object);
    ensures count(pool_slot(pool)) == old(count(pool_slot(pool))) - 1;
    ensures count(pool_object(pool, _)) == old(count(pool_object(pool, _))) + 1;
    ensures pool->checked_out == old(pool->checked_out) + 1;
    ensures pool->capacity == old(pool->capacity);
    ensures valid_pool(pool);
    ensures object->value == old(object->value);
} by {
    open(pool_control(pool)) {
        have 1 <= count(pool_slot(pool)) by simp;
        apply(int32_move_one_from_right_to_left_preserves_sum(
            pool->capacity, pool->checked_out, count(pool_slot(pool))
        )) using {
            0 <= pool->checked_out;
            1 <= count(pool_slot(pool));
            pool->capacity == pool->checked_out + count(pool_slot(pool));
        }
        have defined(pool->checked_out + count(pool_slot(pool))) by simp;
        apply(pool_checkout_increment_bound(pool->capacity, pool->checked_out, count(pool_slot(pool)))) using {
            1 <= count(pool_slot(pool));
            0 <= pool->checked_out;
            pool->capacity == pool->checked_out + count(pool_slot(pool));
            defined(pool->checked_out + count(pool_slot(pool)));
        }
        have 0 <= to_integer(pool->checked_out) by {
            apply(int32_less_equal_to_integer(0, pool->checked_out)) using { 0 <= pool->checked_out; }
            simp();
        }
        have to_integer(pool->checked_out) + 1 >= -2147483648 by {
            arithmetic() using { 0 <= to_integer(pool->checked_out); }
        }
        apply(int32_add_defined_by_integer_bounds(pool->checked_out, 1)) using {
            to_integer(pool->checked_out) + 1 <= 2147483647;
            to_integer(pool->checked_out) + 1 >= -2147483648;
        }
        have defined(pool->checked_out + 1) by simp;
        have pool->checked_out >= 0 by {
            arithmetic() using { 0 <= pool->checked_out; }
        }
        have defined(count(pool_object(pool, _)) + 1) by {
            rewrite(count(pool_object(pool, _)) == pool->checked_out);
            simp();
        }
        unfold(pool_slot(pool));
        step();
        fold(pool_object(pool, object));
        have pool->capacity == pool->checked_out + count(pool_slot(pool)) by simp;
    }
    execute(); unfold(valid_pool); simp();
}

void pool_return(struct pool* pool, struct object* object) {
    owns pool_control(pool);
    requires count(pool_object(pool, object)) == 1;
    consumes pool_object(pool, object);
    produces *object;
    produces pool_slot(pool);
    ensures count(pool_slot(pool)) == old(count(pool_slot(pool))) + 1;
    ensures count(pool_object(pool, _)) == old(count(pool_object(pool, _))) - 1;
    ensures pool->checked_out == old(pool->checked_out) - 1;
    ensures pool->capacity == old(pool->capacity);
    ensures defined(pool->checked_out + count(pool_slot(pool)));
    ensures pool->capacity == pool->checked_out + count(pool_slot(pool));
    ensures valid_pool(pool);
    ensures object->value == old(object->value);
} by {
    open(pool_control(pool)) {
        have 1 <= count(pool_object(pool, _)) by simp;
        have 1 <= pool->checked_out by {
            rewrite(pool->checked_out == count(pool_object(pool, _)));
            assumption();
        }
        have pool->capacity == count(pool_slot(pool)) + pool->checked_out by simp;
        apply(int32_move_one_from_right_to_left_preserves_sum(
            pool->capacity, count(pool_slot(pool)), pool->checked_out
        )) using {
            0 <= count(pool_slot(pool));
            1 <= pool->checked_out;
            pool->capacity == count(pool_slot(pool)) + pool->checked_out;
        }
        have 0 < pool->checked_out by simp;
        have defined(pool->checked_out + count(pool_slot(pool))) by simp;
        apply(int32_add_to_integer(pool->checked_out, count(pool_slot(pool)))) using {
            defined(pool->checked_out + count(pool_slot(pool)));
        }
        have to_integer(pool->capacity) == to_integer(pool->checked_out) + to_integer(count(pool_slot(pool))) by {
            rewrite(pool->capacity == pool->checked_out + count(pool_slot(pool)));
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
        have to_integer(count(pool_slot(pool))) + 1 <= 2147483647 by {
            arithmetic_certificate {
                premise 0: to_integer(pool->capacity) == to_integer(pool->checked_out) + to_integer(count(pool_slot(pool))) => to_integer(pool->capacity) == to_integer(pool->checked_out) + to_integer(count(pool_slot(pool)));
                scale 0 by -1 => -to_integer(pool->capacity) == -to_integer(pool->checked_out) - to_integer(count(pool_slot(pool)));
                eq_to_le 1 => -to_integer(pool->capacity) <= -to_integer(pool->checked_out) - to_integer(count(pool_slot(pool)));
                premise 1: to_integer(pool->capacity) <= 2147483647 => to_integer(pool->capacity) <= 2147483647;
                add 2, 3 => -to_integer(pool->capacity) + to_integer(pool->capacity) <= -to_integer(pool->checked_out) - to_integer(count(pool_slot(pool))) + 2147483647;
                premise 2: 1 <= to_integer(pool->checked_out) => 1 <= to_integer(pool->checked_out);
                add 4, 5 => -to_integer(pool->capacity) + to_integer(pool->capacity) + 1 <= -to_integer(pool->checked_out) - to_integer(count(pool_slot(pool))) + 2147483647 + to_integer(pool->checked_out);
                conclusion 6;
            }
        }
        have 0 <= to_integer(count(pool_slot(pool))) by {
            apply(int32_less_equal_to_integer(0, count(pool_slot(pool)))) using { 0 <= count(pool_slot(pool)); }
            simp();
        }
        have to_integer(count(pool_slot(pool))) + 1 >= -2147483648 by {
            arithmetic() using { 0 <= to_integer(count(pool_slot(pool))); }
        }
        have defined(count(pool_slot(pool)) + 1) by {
            apply(int32_add_defined_by_integer_bounds(count(pool_slot(pool)), 1)) using {
                to_integer(count(pool_slot(pool))) + 1 >= -2147483648;
                to_integer(count(pool_slot(pool))) + 1 <= 2147483647;
            }
            simp();
        }
        unfold(pool_object(pool, object));
        step();
        fold(pool_slot(pool));
        have pool->capacity == old(pool->capacity) by simp;
        have pool->checked_out == old(pool->checked_out) - 1 by simp;
        have count(pool_slot(pool)) == old(count(pool_slot(pool))) + 1 by simp;
        have 0 <= pool->checked_out by {
            rewrite(pool->checked_out == old(pool->checked_out) - 1);
            apply(int32_positive_predecessor_is_nonnegative(old(pool->checked_out))) using { 0 < old(pool->checked_out); }
            assumption();
        }
        have pool->checked_out == count(pool_object(pool, _)) by simp;
        have pool->capacity == pool->checked_out + count(pool_slot(pool)) by {
            rewrite(pool->capacity == old(pool->capacity));
            rewrite(pool->checked_out == old(pool->checked_out) - 1);
            rewrite(count(pool_slot(pool)) == old(count(pool_slot(pool))) + 1);
            rewrite(old(pool->capacity) == (old(count(pool_slot(pool))) + 1) + (old(pool->checked_out) - 1));
            normalize();
        }
    }
    execute(); unfold(valid_pool); simp();
}

void pool_pipeline(struct pool* pool, struct object* first, struct object* second) {
    consumes pool_storage(pool);
    requires count(pool_slot(pool)) == 0;
    requires count(pool_object(pool, _)) == 0;
    owns *first;
    owns *second;
    produces *pool;
    ensures pool->checked_out == 0;
    ensures pool->capacity == 0;
    ensures count(pool_slot(pool)) == 0;
    ensures count(pool_object(pool, _)) == 0;
    ensures first->value == 11;
    ensures second->value == 22;
    ensures valid_pool(pool);
} by {
    step();
    have count(pool_object(pool, _)) == 0 by simp;
    have defined(count(pool_object(pool, _)) + 1) by simp;
    step();
    have count(pool_object(pool, _)) == 1 by simp;
    have defined(count(pool_object(pool, _)) + 1) by simp;
    step();
    open(pool_object(pool, first)) { step(); }
    open(pool_object(pool, second)) { step(); }
    have count(pool_object(pool, second)) == 1 by simp;
    step();
    have count(pool_object(pool, first)) == 1 by simp;
    step();
    unfold(pool_control(pool));
    have pool->capacity == count(pool_slot(pool)) by simp;
    have count(pool_object(pool, _)) == 0 by simp;
    fold(pool_control(pool));
    step();
    execute(); unfold(valid_pool); simp();
}

void pool_shrink(struct pool* pool, int32 amount) {
    owns pool_control(pool);
    consumes amount of pool_slot(pool);
    requires 0 <= amount;
    requires amount <= count(pool_slot(pool));
    requires defined(pool->capacity - amount);
    ensures pool->capacity == old(pool->capacity) - amount;
    ensures pool->checked_out == old(pool->checked_out);
    ensures count(pool_slot(pool)) == old(count(pool_slot(pool))) - amount;
    ensures count(pool_object(pool, _)) == old(count(pool_object(pool, _)));
    ensures valid_pool(pool);
} by {
    open(pool_control(pool)) {
        have defined(pool->checked_out + count(pool_slot(pool))) by simp;
        apply(pool_shrink_sum_defined(pool->capacity, pool->checked_out, count(pool_slot(pool)), amount)) using {
            0 <= pool->checked_out;
            0 <= amount;
            amount <= count(pool_slot(pool));
            pool->capacity == pool->checked_out + count(pool_slot(pool));
            defined(pool->checked_out + count(pool_slot(pool)));
        }
        apply(pool_shrink_conservation(pool->capacity, pool->checked_out, count(pool_slot(pool)), amount)) using {
            0 <= pool->checked_out;
            0 <= amount;
            amount <= count(pool_slot(pool));
            pool->capacity == pool->checked_out + count(pool_slot(pool));
            defined(pool->checked_out + count(pool_slot(pool)));
            defined(pool->capacity - amount);
        }
        unfold(amount of pool_slot(pool));
        step();
        have defined(pool->checked_out + count(pool_slot(pool))) by simp;
        have pool->capacity == old(pool->capacity) - amount by simp;
        have pool->checked_out == old(pool->checked_out) by simp;
        have count(pool_slot(pool)) == old(count(pool_slot(pool))) - amount by simp;
        have pool->capacity == pool->checked_out + count(pool_slot(pool)) by {
            rewrite(pool->capacity == old(pool->capacity) - amount);
            rewrite(pool->checked_out == old(pool->checked_out));
            rewrite(count(pool_slot(pool)) == old(count(pool_slot(pool))) - amount);
            assumption();
        }
    }
    execute(); unfold(valid_pool); simp();
}

void pool_resize_pipeline(struct pool* pool) {
    consumes pool_storage(pool);
    requires count(pool_slot(pool)) == 0;
    requires count(pool_object(pool, _)) == 0;
    produces *pool;
    ensures pool->checked_out == 0;
    ensures pool->capacity == 0;
    ensures count(pool_slot(pool)) == 0;
    ensures count(pool_object(pool, _)) == 0;
    ensures valid_pool(pool);
} by {
    step();
    step();
    unfold(pool_control(pool));
    have pool->capacity == count(pool_slot(pool)) by simp;
    have count(pool_object(pool, _)) == 0 by simp;
    fold(pool_control(pool));
    step();
    execute(); unfold(valid_pool); simp();
}

void pool_grow(struct pool* pool, int32 amount) {
    owns pool_control(pool);
    requires 0 <= amount;
    requires defined(pool->capacity + amount);
    produces amount of pool_slot(pool);
    ensures pool->capacity == old(pool->capacity) + amount;
    ensures pool->checked_out == old(pool->checked_out);
    ensures count(pool_slot(pool)) == old(count(pool_slot(pool))) + amount;
    ensures count(pool_object(pool, _)) == old(count(pool_object(pool, _)));
    ensures valid_pool(pool);
} by {
    open(pool_control(pool)) {
        have defined(pool->checked_out + count(pool_slot(pool))) by simp;
        have 0 <= count(pool_slot(pool)) by simp;
        apply(pool_grow_slots_defined(pool->capacity, pool->checked_out, count(pool_slot(pool)), amount)) using {
            0 <= pool->checked_out; 0 <= count(pool_slot(pool)); 0 <= amount;
            pool->capacity == pool->checked_out + count(pool_slot(pool));
            defined(pool->checked_out + count(pool_slot(pool))); defined(pool->capacity + amount);
        }
        have defined(count(pool_slot(pool)) + amount) by simp;
        apply(pool_grow_conservation(pool->capacity, pool->checked_out, count(pool_slot(pool)), amount)) using {
            0 <= pool->checked_out; 0 <= count(pool_slot(pool)); 0 <= amount;
            pool->capacity == pool->checked_out + count(pool_slot(pool));
            defined(pool->checked_out + count(pool_slot(pool))); defined(pool->capacity + amount);
        }
        step();
        fold(amount of pool_slot(pool));
        have pool->capacity == old(pool->capacity) + amount by simp;
        have pool->checked_out == old(pool->checked_out) by simp;
        have count(pool_slot(pool)) == old(count(pool_slot(pool))) + amount by simp;
        have defined(pool->checked_out + count(pool_slot(pool))) by simp;
        have pool->capacity == pool->checked_out + count(pool_slot(pool)) by {
            rewrite(pool->capacity == old(pool->capacity) + amount);
            rewrite(pool->checked_out == old(pool->checked_out));
            rewrite(count(pool_slot(pool)) == old(count(pool_slot(pool))) + amount);
            assumption();
        }
    }
    execute(); unfold(valid_pool); simp();
}

void pool_transfer(struct pool* source, struct pool* destination, struct object* object) {
    requires source != destination;
    owns pool_control(source);
    owns pool_control(destination);
    requires count(pool_object(source, object)) == 1;
    requires count(pool_object(destination, object)) == 0;
    consumes pool_object(source, object);
    consumes pool_slot(destination);
    produces pool_object(destination, object);
    produces pool_slot(source);
    ensures count(pool_object(source, _)) == old(count(pool_object(source, _))) - 1;
    ensures count(pool_object(destination, _)) == old(count(pool_object(destination, _))) + 1;
    ensures count(pool_slot(source)) == old(count(pool_slot(source))) + 1;
    ensures count(pool_slot(destination)) == old(count(pool_slot(destination))) - 1;
    ensures source->checked_out == old(source->checked_out) - 1;
    ensures destination->checked_out == old(destination->checked_out) + 1;
    ensures source->capacity == old(source->capacity);
    ensures destination->capacity == old(destination->capacity);
    ensures object->value == old(object->value);
    ensures valid_pool(source);
    ensures valid_pool(destination);
} by {
    open(pool_control(source)) {
        open(pool_control(destination)) {
            have 1 <= count(pool_object(source, _)) by simp;
            have 1 <= source->checked_out by {
                rewrite(source->checked_out == count(pool_object(source, _)));
                assumption();
            }
            have source->capacity == count(pool_slot(source)) + source->checked_out by simp;
            apply(int32_move_one_from_right_to_left_preserves_sum(
                source->capacity, count(pool_slot(source)), source->checked_out
            )) using {
                0 <= count(pool_slot(source));
                1 <= source->checked_out;
                source->capacity == count(pool_slot(source)) + source->checked_out;
            }
            have 0 < source->checked_out by simp;
            have defined(source->checked_out + count(pool_slot(source))) by simp;
            apply(int32_add_to_integer(source->checked_out, count(pool_slot(source)))) using {
                defined(source->checked_out + count(pool_slot(source)));
            }
            have to_integer(source->capacity) == to_integer(source->checked_out) + to_integer(count(pool_slot(source))) by {
                rewrite(source->capacity == source->checked_out + count(pool_slot(source)));
                assumption();
            }
            have source->capacity <= 2147483647 by simp;
            have to_integer(source->capacity) <= 2147483647 by {
                apply(int32_less_equal_to_integer(source->capacity, 2147483647)) using { source->capacity <= 2147483647; }
                simp();
            }
            have 1 <= to_integer(source->checked_out) by {
                apply(int32_less_equal_to_integer(1, source->checked_out)) using { 1 <= source->checked_out; }
                simp();
            }
            have to_integer(count(pool_slot(source))) + 1 <= 2147483647 by {
                arithmetic_certificate {
                    premise 0: to_integer(source->capacity) == to_integer(source->checked_out) + to_integer(count(pool_slot(source))) => to_integer(source->capacity) == to_integer(source->checked_out) + to_integer(count(pool_slot(source)));
                    scale 0 by -1 => -to_integer(source->capacity) == -to_integer(source->checked_out) - to_integer(count(pool_slot(source)));
                    eq_to_le 1 => -to_integer(source->capacity) <= -to_integer(source->checked_out) - to_integer(count(pool_slot(source)));
                    premise 1: to_integer(source->capacity) <= 2147483647 => to_integer(source->capacity) <= 2147483647;
                    add 2, 3 => -to_integer(source->capacity) + to_integer(source->capacity) <= -to_integer(source->checked_out) - to_integer(count(pool_slot(source))) + 2147483647;
                    premise 2: 1 <= to_integer(source->checked_out) => 1 <= to_integer(source->checked_out);
                    add 4, 5 => -to_integer(source->capacity) + to_integer(source->capacity) + 1 <= -to_integer(source->checked_out) - to_integer(count(pool_slot(source))) + 2147483647 + to_integer(source->checked_out);
                    conclusion 6;
                }
            }
            have 0 <= to_integer(count(pool_slot(source))) by {
                apply(int32_less_equal_to_integer(0, count(pool_slot(source)))) using { 0 <= count(pool_slot(source)); }
                simp();
            }
            have to_integer(count(pool_slot(source))) + 1 >= -2147483648 by {
                arithmetic() using { 0 <= to_integer(count(pool_slot(source))); }
            }
            have defined(count(pool_slot(source)) + 1) by {
                apply(int32_add_defined_by_integer_bounds(count(pool_slot(source)), 1)) using {
                    to_integer(count(pool_slot(source))) + 1 >= -2147483648;
                    to_integer(count(pool_slot(source))) + 1 <= 2147483647;
                }
                simp();
            }
            have 1 <= count(pool_slot(destination)) by simp;
            apply(int32_move_one_from_right_to_left_preserves_sum(
                destination->capacity, destination->checked_out, count(pool_slot(destination))
            )) using {
                0 <= destination->checked_out;
                1 <= count(pool_slot(destination));
                destination->capacity == destination->checked_out + count(pool_slot(destination));
            }
            have defined(destination->checked_out + count(pool_slot(destination))) by simp;
            apply(pool_checkout_increment_bound(destination->capacity, destination->checked_out, count(pool_slot(destination)))) using {
                1 <= count(pool_slot(destination));
                0 <= destination->checked_out;
                destination->capacity == destination->checked_out + count(pool_slot(destination));
                defined(destination->checked_out + count(pool_slot(destination)));
            }
            have 0 <= to_integer(destination->checked_out) by {
                apply(int32_less_equal_to_integer(0, destination->checked_out)) using { 0 <= destination->checked_out; }
                simp();
            }
            have to_integer(destination->checked_out) + 1 >= -2147483648 by {
                arithmetic() using { 0 <= to_integer(destination->checked_out); }
            }
            apply(int32_add_defined_by_integer_bounds(destination->checked_out, 1)) using {
                to_integer(destination->checked_out) + 1 <= 2147483647;
                to_integer(destination->checked_out) + 1 >= -2147483648;
            }
            have defined(destination->checked_out + 1) by simp;
            have destination->checked_out >= 0 by {
                arithmetic() using { 0 <= destination->checked_out; }
            }
            have defined(count(pool_object(destination, _)) + 1) by {
                rewrite(count(pool_object(destination, _)) == destination->checked_out);
                simp();
            }
            unfold(pool_object(source, object));
            unfold(pool_slot(destination));
            step();
            step();
            fold(pool_object(destination, object));
            fold(pool_slot(source));
            have source->capacity == old(source->capacity) by simp;
            have source->checked_out == old(source->checked_out) - 1 by simp;
            have count(pool_slot(source)) == old(count(pool_slot(source))) + 1 by simp;
            have 0 <= source->checked_out by {
                rewrite(source->checked_out == old(source->checked_out) - 1);
                apply(int32_positive_predecessor_is_nonnegative(old(source->checked_out))) using { 0 < old(source->checked_out); }
                assumption();
            }
            have source->checked_out == count(pool_object(source, _)) by simp;
            have source->capacity == source->checked_out + count(pool_slot(source)) by {
                rewrite(source->capacity == old(source->capacity));
                rewrite(source->checked_out == old(source->checked_out) - 1);
                rewrite(count(pool_slot(source)) == old(count(pool_slot(source))) + 1);
                rewrite(old(source->capacity) == (old(count(pool_slot(source))) + 1) + (old(source->checked_out) - 1));
                normalize();
            }
            have destination->capacity == destination->checked_out + count(pool_slot(destination)) by simp;
        }
    }
    execute(); unfold(valid_pool); simp();
}

void pool_transfer_pipeline(struct pool* source, struct pool* destination, struct object* object) {
    requires source != destination;
    consumes pool_storage(source);
    consumes pool_storage(destination);
    consumes *object;
    requires count(pool_slot(source)) == 0;
    requires count(pool_slot(destination)) == 0;
    requires count(pool_object(source, _)) == 0;
    requires count(pool_object(destination, _)) == 0;
    produces pool_control(source);
    produces pool_control(destination);
    produces pool_object(destination, object);
    produces pool_slot(source);
    ensures valid_pool(source);
    ensures valid_pool(destination);
    ensures source->checked_out == 0;
    ensures source->capacity == 1;
    ensures destination->checked_out == 1;
    ensures destination->capacity == 1;
    ensures count(pool_object(source, _)) == 0;
    ensures count(pool_object(destination, _)) == 1;
    ensures count(pool_slot(source)) == 1;
    ensures count(pool_slot(destination)) == 0;
    ensures object->value == old(object->value);
} by {
    open(pool_storage(source)) {
        open(pool_storage(destination)) {
            have object->value == old(object->value) by simp;
        }
    }
    step();
    have object->value == old(object->value) by simp;
    open(pool_control(source)) { step(); }
    have object->value == old(object->value) by simp;
    have count(pool_object(source, _)) == 0 by simp;
    have defined(count(pool_object(source, _)) + 1) by simp;
    open(pool_control(destination)) { step(); }
    have object->value == old(object->value) by simp;
    have count(pool_object(source, object)) == 1 by simp;
    have count(pool_object(destination, object)) == 0 by simp;
    have count(pool_slot(source)) == 0 by simp;
    have count(pool_object(destination, _)) == 0 by simp;
    have defined(count(pool_slot(source)) + 1) by simp;
    have defined(count(pool_object(destination, _)) + 1) by simp;
    step();
    execute(); unfold(valid_pool); simp();
}
