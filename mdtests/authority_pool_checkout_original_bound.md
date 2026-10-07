# Ordinary checkout helpers derive their count bound from the control

The first C block is unchanged from `examples/bounded-pool/pool_checkout.c`.
The direct and nested helper contracts preserve `valid_pool` without an extra
counter-bound requirement. Before each call, the proof opens the control,
establishes population increment safety, and closes it again. The C helpers
remain ordinary calls.

```c filename=pool_checkout.c
struct pool {
    int32 checked_out;
    int32 capacity;
};

struct object {
    int32 value;
};

void pool_checkout(struct pool* pool, struct object* object) {
    pool->checked_out = pool->checked_out + 1;
}
```

```c filename=checkout_helpers.c
struct pool { int32 checked_out; int32 capacity; };
struct object { int32 value; };
void pool_checkout(struct pool* pool, struct object* object);
void forward(struct pool* pool, struct object* object) {
    pool_checkout(pool, object);
}
void caller(struct pool* pool, struct object* object) {
    forward(pool, object);
}


```

```click resource_semantics=authority
authorized resource pool_slot(pool: struct pool*) {}
authorized resource pool_object(pool: struct pool*, object: struct object*) { owns object(object); }
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
verifying "pool_checkout.c";
verifying "checkout_helpers.c";
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

void forward(struct pool* pool, struct object* object) {
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
        have pool->checked_out >= 0 by {
            arithmetic() using { 0 <= pool->checked_out; }
        }
        have defined(count(pool_object(pool, _)) + 1) by {
            rewrite(count(pool_object(pool, _)) == pool->checked_out);
            simp();
        }
    }
    execute(); unfold(valid_pool); simp();
}

void caller(struct pool* pool, struct object* object) {
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
        have pool->checked_out >= 0 by {
            arithmetic() using { 0 <= pool->checked_out; }
        }
        have defined(count(pool_object(pool, _)) + 1) by {
            rewrite(count(pool_object(pool, _)) == pool->checked_out);
            simp();
        }
    }
    execute(); unfold(valid_pool); simp();
}

```

```expect
pass
```
