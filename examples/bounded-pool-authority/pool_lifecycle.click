resource pool_slot(pool: struct pool*) {}
resource pool_object(pool: struct pool*, object: struct object*) { owns object(object); }
resource pool_storage(pool: struct pool*) {
    owns object(pool);
    owns authority(pool_slot(pool));
    owns authority(pool_object(pool, _));
}
resource pool_control(pool: struct pool*) {
    owns object(pool);
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
predicate valid_pool(pool: struct pool*) {
    0 <= pool->checked_out and
    pool->checked_out == count(pool_object(pool, _)) and
    pool->capacity == pool->checked_out + count(pool_slot(pool))
}
verifying "../bounded-pool/pool_init.c";
verifying "../bounded-pool/pool_destroy.c";
verifying "../bounded-pool/pool_zero_pipeline.c";
verifying "../bounded-pool/pool_checkout.c";
verifying "../bounded-pool/pool_return.c";
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
    produces object(pool);
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
    produces object(pool);
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
    consumes object(object);
    produces pool_object(pool, object);
    ensures count(pool_slot(pool)) == old(count(pool_slot(pool))) - 1;
    ensures count(pool_object(pool, _)) == old(count(pool_object(pool, _))) + 1;
    ensures pool->checked_out == old(pool->checked_out) + 1;
    ensures pool->capacity == old(pool->capacity);
    ensures valid_pool(pool);
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
    produces object(object);
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
