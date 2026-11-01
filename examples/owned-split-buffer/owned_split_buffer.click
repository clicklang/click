theorem incremented_one_is_two(before: int32, after: int32) {
    requires before == 1;
    requires after == before + 1;

    ensures after == 2 by {
        rewrite(after == before + 1);
        rewrite(before == 1);
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

resource owned_split_buffer(owner: struct owned_split_buffer*) {
    owns *owner;
    owns owner->data[0..owner->split];
    owns owner->data[owner->split..owner->len];
    fact 0 <= owner->split;
    fact owner->split <= owner->len;
    fact separate(
        memory(*owner),
        memory(owner->data[0..owner->len])
    );
}

verifying "owned_split_buffer_init.c";
verifying "owned_split_buffer_set_left.c";
verifying "owned_split_buffer_set_right.c";
verifying "owned_split_buffer_move_right.c";
verifying "owned_split_buffer_get_left.c";
verifying "owned_split_buffer_pipeline.c";

int32 owned_split_buffer_init(
    struct owned_split_buffer* owner,
    int32 data[],
    int32 length,
    int32 split
) {
    requires 0 <= split;
    requires split <= length;
    consumes *owner;
    consumes data[0..length];
    produces owned_split_buffer(owner);
    ensures result == split;
    ensures owner->split == split;
    ensures owner->len == length;
    ensures owner->data == data;
} by {
    step_until(function.exit);
    fold(owned_split_buffer(owner));
    solve();
}

int32 owned_split_buffer_set_left(
    struct owned_split_buffer* owner,
    int32 index,
    int32 value
) {
    requires 0 <= index;
    requires index < owner->split;
    requires 0 <= owner->split;
    requires owner->split <= owner->len;
    requires separate(
        memory(*owner),
        memory(owner->data[0..owner->len])
    );
    views *owner;
    owns owner->data[index..index + 1];
    ensures result == value;
    ensures owner->data[index] == value;
    ensures owner->split == old(owner->split);
    ensures owner->len == old(owner->len);
    ensures owner->data == old(owner->data);
} by {
    mark before_store;
    have separate(memory(owner->data[index]), memory(owner->data));
    step();
    have separate(statement(0).footprint, memory(owner->data)) by {
        normalize() using {
            at(before_store, separate(memory(owner->data[index]), memory(owner->data)));
        };
    }
    have owner->data == at(before_store, owner->data) by {
        transport_certificate {
            premise 0: separate(statement(0).footprint, memory(owner->data))
                => separate(statement(0).footprint, memory(owner->data));
            preserve 0 => owner->data == at(before_store, owner->data);
            conclusion 1;
        }
    }
    step();
    solve();
}

int32 owned_split_buffer_set_right(
    struct owned_split_buffer* owner,
    int32 index,
    int32 value
) {
    requires owner->split <= index;
    requires index < owner->len;
    requires 0 <= owner->split;
    requires owner->split <= owner->len;
    requires separate(
        memory(*owner),
        memory(owner->data[0..owner->len])
    );
    views *owner;
    owns owner->data[index..index + 1];
    ensures result == value;
    ensures owner->data[index] == value;
    ensures owner->split == old(owner->split);
    ensures owner->len == old(owner->len);
    ensures owner->data == old(owner->data);
} by {
    step();
    step();
    solve();
}

int32 owned_split_buffer_move_right(struct owned_split_buffer* owner) {
    requires owner->split < owner->len;
    views owner->len;
    views owner->data;
    owns owner->split;
    ensures result == old(owner->split) + 1;
    ensures owner->split == old(owner->split) + 1;
    ensures owner->len == old(owner->len);
    ensures owner->data == old(owner->data);
} by {
    step();
    step();
    solve();
}

int32 owned_split_buffer_get_left(
    struct owned_split_buffer* owner,
    int32 index
) {
    requires 0 <= index;
    requires index < owner->split;
    views owned_split_buffer(owner);

    ensures result == owner->data[index];
}

int32 owned_split_buffer_pipeline(
    struct owned_split_buffer* owner,
    int32 data[],
    int32 length,
    int32 left_value,
    int32 right_value
) {
    requires 2 <= length;
    consumes *owner;
    consumes data[0..length];
    produces owned_split_buffer(owner);
    ensures owner->split == 2;
    ensures owner->len == length;
    ensures owner->data == data;
    ensures data[0] == left_value;
    ensures data[1] == right_value;
    ensures result == right_value;
} by {
    step();
    step();
    step();
    unfold(owned_split_buffer(owner));
    step();
    transport(at(region(3).entry, owner->split) == 1, owner->split == 1) using {
        at(region(3).entry, owner->split) == 1;
        2 <= length;
        at(region(3).entry, owner->data) == data;
    };
    transport(at(region(3).entry, owner->len) == length, owner->len == length) using {
        at(region(3).entry, owner->len) == length;
        2 <= length;
        at(region(3).entry, owner->data) == data;
    };
    transport(at(region(3).entry, owner->data) == data, owner->data == data) using {
        at(region(3).entry, owner->data) == data;
        2 <= length;
    };
    have 1 < length by {
        arithmetic_certificate {
            premise 0: at(function.entry, 2 <= length) => at(function.entry, 2 <= length);
            conclusion 0;
        }
    }
    have 1 < owner->len by {
        assumption();
    }
    step();
    transport(at(region(4).entry, owner->data) == data, owner->data == data) using {
        at(region(4).entry, owner->data) == data;
        2 <= length;
    };
    transport(at(region(4).entry, 1) < at(region(4).entry, owner->len), 1 < owner->len) using {
        at(region(4).entry, 1) < at(region(4).entry, owner->len);
        owner->data == data;
        2 <= length;
    };
    have data[1] == right_value by {
        normalize() using {
            at(region(5).entry, *(owner->data + 1)) == at(region(5).entry, right_value);
            owner->data == data;
        };
    }
    step();
    have to_integer(at(region(5).exit, owner->split)) == (to_integer(at(region(5).entry, owner->split)) + 1) by {
        assumption();
    }
    apply(incremented_one_is_two(at(region(5).entry, owner->split), at(region(5).exit, owner->split))) using {
        at(region(5).entry, owner->split) == 1;
        to_integer(at(region(5).exit, owner->split)) == (to_integer(at(region(5).entry,
            owner->split)) + 1);
    };
    fold(owned_split_buffer(owner));
    step();
    apply(int32_equality_transitive(c(result), data[1], right_value)) using {
        c(result) == data[1];
        data[1] == right_value;
    };
    step();
    assumption();
    have owner->split == 2 by {
        assumption();
    }
    have owner->len == length by {
        assumption();
    }
    have owner->data == data by {
        assumption();
    }
    have data[0] == left_value by {
        rewrite(data == at(region(3).entry, owner->data));
        assumption();
    }
    have data[1] == right_value by {
        assumption();
    }
    have result == right_value by {
        assumption();
    }
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
}
