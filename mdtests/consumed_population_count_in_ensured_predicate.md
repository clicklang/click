# consumed populations are visible to ensured predicates

An explicit arithmetic lemma carries both the subtraction identity and the
recomposed sum's definedness through the symbolic spend. The lemma is proved
from the existing contract conditions; the C and contract remain unchanged.

A symbolic resource consumption and a matching C update preserve a predicate
that relates concrete state to the post-state population count. Independent
contract certification must use the same checked population transition as the
explicit proof.

```c filename=consume_population.c
struct owner {
    int32 used;
    int32 capacity;
};

void consume_population(struct owner* owner, int32 amount) {
    owner->capacity = owner->capacity - amount;
}
```

```click
theorem subtract_from_sum(total: int32, left: int32, right: int32, amount: int32) {
    requires 0 <= left;
    requires 0 <= amount;
    requires amount <= right;
    requires total == left + right;
    requires defined(left + right);
    requires defined(total - amount);
    ensures defined(left + (right - amount)) and
            total - amount == left + (right - amount) by {
        have defined(left + right);
        have defined(right - amount) by {
            apply(int32_nonnegative_subtract_within_value_is_defined(right, amount)) using {
                0 <= amount;
                amount <= right;
            }
            assumption();
        }
        apply(int32_add_to_integer(left, right)) using { defined(left + right); }
        have to_integer(total) == to_integer(left) + to_integer(right) by {
            rewrite(total == left + right);
            assumption();
        }
        apply(int32_subtract_to_integer(right, amount)) using { defined(right - amount); }
        have 0 <= to_integer(left) by {
            apply(int32_less_equal_to_integer(0, left)) using { 0 <= left; }
            simp();
        }
        have 0 <= to_integer(amount) by {
            apply(int32_less_equal_to_integer(0, amount)) using { 0 <= amount; }
            simp();
        }
        have to_integer(amount) <= to_integer(right) by {
            apply(int32_less_equal_to_integer(amount, right)) using { amount <= right; }
            assumption();
        }
        have total <= 2147483647;
        have to_integer(total) <= 2147483647 by {
            apply(int32_less_equal_to_integer(total, 2147483647)) using { total <= 2147483647; }
            simp();
        }
        have to_integer(0) >= -2147483648;
        have 0 <= right - amount by {
            arithmetic() using { 0 <= amount; amount <= right; }
        }
        have 0 <= to_integer(right - amount) by {
            apply(int32_less_equal_to_integer(0, right - amount)) using { 0 <= right - amount; }
            simp();
        }
        have 0 <= to_integer(left) + to_integer(right - amount) by {
            arithmetic() using {
                0 <= to_integer(left);
                0 <= to_integer(right - amount);
            }
        }
        have to_integer(left) + to_integer(right - amount) >= -2147483648 by {
            arithmetic() using {
                0 <= to_integer(left) + to_integer(right - amount);
                to_integer(0) >= -2147483648;
            }
        }
        have to_integer(left) + to_integer(right - amount) + to_integer(amount) == to_integer(total) by {
            arithmetic() using {
                to_integer(total) == to_integer(left) + to_integer(right);
                to_integer(right - amount) == to_integer(right) - to_integer(amount);
            }
        }
        have to_integer(left) + to_integer(right - amount) <= to_integer(total) by {
            arithmetic() using {
                to_integer(left) + to_integer(right - amount) + to_integer(amount) == to_integer(total);
                0 <= to_integer(amount);
            }
        }
        have to_integer(left) + to_integer(right - amount) <= 2147483647 by {
            arithmetic() using {
                to_integer(left) + to_integer(right - amount) <= to_integer(total);
                to_integer(total) <= 2147483647;
            }
        }
        apply(int32_add_defined_by_integer_bounds(left, right - amount)) using {
            to_integer(left) + to_integer(right - amount) >= -2147483648;
            to_integer(left) + to_integer(right - amount) <= 2147483647;
        }
        have defined(left + (right - amount));
        apply(int32_subtract_to_integer(total, amount)) using { defined(total - amount); }
        apply(int32_add_to_integer(left, right - amount)) using { defined(left + (right - amount)); }
        have to_integer(total - amount) == to_integer(left + (right - amount)) by {
            arithmetic() using {
                to_integer(total - amount) == to_integer(total) - to_integer(amount);
                to_integer(left + (right - amount)) == to_integer(left) + to_integer(right - amount);
                to_integer(total) == to_integer(left) + to_integer(right);
                to_integer(right - amount) == to_integer(right) - to_integer(amount);
            }
        }
        apply(int32_equal_of_to_integer(total - amount, left + (right - amount))) using {
            to_integer(total - amount) == to_integer(left + (right - amount));
        }
        simp();
    }
}

authorized resource slot(owner: struct owner*) {
}

authorized abstract resource item(owner: struct owner*, id: int32);

resource accounting(owner: struct owner*) {
    owns owner->used;
    owns owner->capacity;
    owns authority(slot(owner));
    owns authority(item(owner, _));
    fact 0 <= owner->used;
    fact owner->used == count(item(owner, _));
    fact owner->capacity == owner->used + count(slot(owner));
}

predicate valid_capacity(owner: struct owner*) {
    0 <= owner->used and
    owner->used == count(item(owner, _)) and
    owner->capacity == owner->used + count(slot(owner))
}

verifying "consume_population.c";

void consume_population(struct owner* owner, int32 amount) {
    requires valid_capacity(owner);
    requires 0 <= amount;
    requires amount <= count(slot(owner));
    requires defined(owner->capacity - amount);
    owns accounting(owner);
    consumes amount of slot(owner);

    ensures valid_capacity(owner);
} by {
    open(accounting(owner)) {
        unfold(valid_capacity);
        have defined(owner->used + count(slot(owner)));
        apply(subtract_from_sum(owner->capacity, owner->used, count(slot(owner)), amount)) using {
            0 <= owner->used;
            0 <= amount;
            amount <= count(slot(owner));
            owner->capacity == owner->used + count(slot(owner));
            defined(owner->used + count(slot(owner)));
            defined(owner->capacity - amount);
        }
        unfold(amount of slot(owner));
        step();
        have owner->capacity == owner->used + count(slot(owner));
    }
    execute();
    unfold(valid_capacity);
    simp();
}
```

```expect
pass
```
