theorem incremented_zero_is_one(before: int32, after: int32) {
    requires before == 0;
    requires after == before + 1;

    ensures after == 1 by {
        rewrite(after, before + 1);
        rewrite(before, 0);
        solve();
    }
}

theorem decremented_one_is_zero(before: int32, after: int32) {
    requires before == 1;
    requires after == before - 1;

    ensures after == 0 by {
        rewrite(after, before - 1);
        rewrite(before, 1);
        solve();
    }
}

theorem int32_equality_transitive(first: int32, second: int32, third: int32) {
    requires first == second;
    requires second == third;

    ensures first == third by {
        solve();
    }
}

theorem pointer_equality_transitive(
    first: int32*,
    second: int32*,
    third: int32*
) {
    requires first == second;
    requires second == third;

    ensures first == third by {
        solve();
    }
}

theorem pointer_add_zero_equals(
    base: int32*,
    offset: int32,
    target: int32*
) {
    requires base == target;
    requires offset == 0;

    ensures base + offset == target by {
        solve();
    }
}

predicate terminated_at(data: int32[], length: int32) {
    data[length] == 0
}

resource owned_string(owner: struct owned_string*) {
    owns *owner;
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len < owner->cap;
    fact terminated_at(owner->data, owner->len);
    fact separate(
        memory(*owner),
        memory(owner->data[0..owner->cap])
    );
}

resource empty_owned_string(owner: struct owned_string*) {
    owns *owner;
    owns owner->data[0..owner->cap];
    fact owner->len == 0;
    fact owner->len < owner->cap;
    fact terminated_at(owner->data, owner->len);
    fact separate(
        memory(*owner),
        memory(owner->data[0..owner->cap])
    );
}

verifying "owned_string_init.c";
verifying "owned_string_len.c";
verifying "owned_string_get.c";
verifying "owned_string_set.c";
verifying "owned_string_push.c";
verifying "owned_string_push_preserves_first.c";
verifying "owned_string_pop.c";
verifying "owned_string_pop_preserves_first.c";
verifying "owned_string_clear.c";
verifying "owned_string_pipeline.c";

int32 owned_string_init(
    struct owned_string* owner,
    int32 data[],
    int32 capacity
) {
    requires 1 <= capacity;
    consumes *owner;
    consumes data[0..capacity];
    produces owned_string(owner);
    ensures result == 0;
    ensures owner->len == 0;
    ensures owner->cap == capacity;
    ensures owner->data == data;
    ensures data[0] == 0;
} by {
    step();
    step();
    step();
    step();
    step();
    have owner->data == data;
    have owner->len == 0;
    have data[0] == 0;
    have terminated_at(owner->data, owner->len) by {
        unfold(terminated_at(owner->data, owner->len));
        rewrite(owner->data, data);
        rewrite(owner->len, 0);
        known();
    }
    have 0 <= owner->len;
    have owner->len < owner->cap;
    have separate(
        memory(*owner),
        memory(owner->data[0..owner->cap])
    ) by {
        close() using {
            separate(memory(*owner), memory(data[0..capacity]));
            owner->data == data;
            owner->cap == capacity;
        };
    }
    fold(owned_string(owner));
    known();
    known();
    known();
}

int32 owned_string_len(struct owned_string* owner) {
    views owned_string(owner);

    ensures result == owner->len by {
        step();
        known();
    }
}

int32 owned_string_get(struct owned_string* owner, int32 index) {
    requires 0 <= index;
    requires index < owner->len;
    views owned_string(owner);

    ensures result == owner->data[index] by {
        step();
        known();
    }
}

int32 owned_string_set(
    struct owned_string* owner,
    int32 index,
    int32 value
) {
    requires 0 <= index;
    requires index < owner->len;
    owns owned_string(owner);

    ensures result == value;
    ensures owner->data[index] == value;
} by {
    unfold(owned_string(owner));
    unfold(terminated_at(owner->data, owner->len));
    step();
    have separate(
        memory(*owner),
        memory(owner->data[0..owner->cap])
    ) by {
        solve();
    }
    have owner->data[index] == value by {
        solve();
    }
    fold(owned_string(owner));
    step();
    known();
    known();
    known();
}

int32 owned_string_push(struct owned_string* owner, int32 value) {
    requires owner->len + 1 < owner->cap;
    owns owned_string(owner);
    ensures result == old(owner->len) + 1;
    ensures owner->len == old(owner->len) + 1;
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
    ensures owner->data[old(owner->len)] == value;
    ensures owner->data[owner->len] == 0;
} by {
    unfold(owned_string(owner));
    step();
    step();
    step();
    step();
    have 0 <= to_integer(index + 1);
    have to_integer(index + 1) < to_integer(owner->cap);
    step();
    have owner->len == at(region(4).entry, (index + 1));
    step();
    have 0 <= old(owner->len) + 1 by {
        close() using {
            0 <= old(owner->len);
            old(owner->len) < old(owner->cap);
            old(owner->cap) <= 1073741823;
        }
    }
    have owner->data == old(owner->data) by {
        solve();
    }
    have terminated_at(owner->data, owner->len) by {
        unfold(terminated_at(owner->data, owner->len));
        solve();
    }
    fold(owned_string(owner));
    have owner->len == (old(owner->len) + 1) by {
        rewrite(owner->len, at(region(3).entry, (index + 1)));
        known();
    }
    known();
    known();
    known();
    known();
    known();
    known();
    known();
}

int32 owned_string_push_preserves_first(
    struct owned_string* owner,
    int32 value
) {
    let data = old(owner->data);

    requires 1 <= owner->len;
    requires owner->len + 1 < owner->cap;
    owns owned_string(owner);

    ensures result == old(owner->len) + 1;
    ensures data[0] == old(data[0]);
} by {
    step();
    step();
    step();
    step();
    known();
    known();
    known();
}

int32 owned_string_pop(struct owned_string* owner) {
    requires 1 <= owner->len;
    owns owned_string(owner);
    ensures result == old(owner->data[owner->len - 1]);
    ensures owner->len == old(owner->len) - 1;
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
    ensures owner->data[owner->len] == 0;
} by {
    unfold(owned_string(owner));
    have 0 <= to_integer(owner->len - 1);
    have to_integer(owner->len - 1) < to_integer(owner->len);
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    have terminated_at(owner->data, owner->len) by {
        unfold(terminated_at(owner->data, owner->len));
        known();
    }
    fold(owned_string(owner));
    have owner->data[owner->len] == 0;
    solve();
}

int32 owned_string_pop_preserves_first(struct owned_string* owner) {
    let data = old(owner->data);

    requires 2 <= owner->len;
    owns owned_string(owner);

    ensures result == old(owner->data[owner->len - 1]);
    ensures data[0] == old(data[0]);
} by {
    step();
    step();
    step();
    step();
    known();
    known();
    known();
}

int32 owned_string_clear(struct owned_string* owner) {
    owns owned_string(owner);
    ensures result == 0;
    ensures owner->len == 0;
    ensures owner->data[0] == 0;
} by {
    unfold(owned_string(owner));
    have 0 < owner->cap by {
        close() using { 0 <= owner->len; owner->len < owner->cap; };
    }
    step();
    step();
    step();
    have terminated_at(owner->data, owner->len);
    have 0 <= owner->len;
    have separate(
        memory(*owner),
        memory(owner->data[0..owner->cap])
    ) by {
        solve();
    }
    have owner->len == 0;
    have owner->len < owner->cap by {
        rewrite(owner->len, 0);
        known();
    }
    fold(owned_string(owner));
    known();
    known();
    known();
    known();
}

int32 owned_string_pipeline(
    struct owned_string* owner,
    int32 data[],
    int32 capacity,
    int32 first
) {
    requires 2 <= capacity;
    consumes *owner;
    consumes data[0..capacity];
    produces empty_owned_string(owner);
    ensures result == first;
} by {
    step();
    step();
    step();
    step();
    have ignored == 0 by {
        known();
    }
    have owner->len == 0 by {
        known();
    }
    have owner->cap == capacity by {
        known();
    }
    have (owner->len + 1) < owner->cap by {
        rewrite(owner->cap, capacity);
        rewrite(owner->len, 0);
        have 1 < at(statement(2).entry, capacity);
        solve();
    }
    step();
    step();
    have owner->len == 1 by {
        rewrite(owner->len, at(statement(3).entry, owner->len + 1));
        rewrite(at(statement(3).entry, owner->len), at(statement(3).entry, 0));
        known();
    }
    have 0 < owner->len by {
        rewrite(owner->len, 1);
        known();
    }
    have owner->data[at(statement(3).entry, owner->len)] == first by {
        known();
    }
    have owner->data[0] == first by {
        rewrite(first, owner->data[at(statement(3).entry, owner->len)]);
        rewrite(at(statement(3).entry, owner->len), at(statement(3).entry, 0));
        known();
    }
    step();
    step();
    have 1 <= owner->len by {
        rewrite(owner->len, 1);
        known();
    }
    have observed == first by {
        rewrite(first, owner->data[0]);
        known();
    }
    step();
    step();
    have owner->len == at(statement(5).entry, owner->len) - 1 by {
        known();
    }
    have at(statement(5).entry, owner->len) == 1 by {
        known();
    }
    apply(decremented_one_is_zero(at(statement(5).entry, owner->len), owner->len));
    have owner->len == 0 by {
        known();
    }
    unfold(owned_string(owner));
    fold(empty_owned_string(owner));
    have observed == first by {
        known();
    }
    step();
    have result == at(statement(6).entry, observed) by {
        known();
    }
    have at(statement(6).entry, observed) == first by {
        known();
    }
    have result == first by {
        known();
    }
    known();
    known();
}
