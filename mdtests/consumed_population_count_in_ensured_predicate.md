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
import click::integer;

theorem subtract_from_sum(total: int32, left: int32, right: int32, amount: int32) {
    requires 0 <= left;
    requires 0 <= amount;
    requires amount <= right;
    requires total == left + right;
    requires defined(left + right);
    requires defined(total - amount);
    ensures defined(left + (right - amount)) and
            total - amount == left + (right - amount) by {
        auto();
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
        have defined(owner->used + count(slot(owner))) by auto();
        apply(subtract_from_sum(owner->capacity, owner->used, count(slot(owner)), amount)) using {
            0 <= owner->used;
            0 <= amount;
            amount <= count(slot(owner));
            owner->capacity == owner->used + count(slot(owner));
            defined(owner->used + count(slot(owner)));
            defined(owner->capacity - amount);
        };
        unfold(amount of slot(owner));
        step();
        have owner->capacity == owner->used + count(slot(owner)) by auto();
    }
    execute();
    unfold(valid_capacity);
    simp();
}
```

```expect
pass
```
