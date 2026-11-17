import click::separation;

theorem incremented_one_is_two(before: int32, after: int32) {
    requires before == 1;
    requires after == before + 1;

    ensures after == 2 by {
        rewrite(after, before + 1);
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
    have index <= ((index + 1) as int32);
    have ((index + 1) as int32) <= owner->len;
    have contains(memory(owner->data[0..owner->len]), memory(owner->data[index..index + 1])) by {
        apply(separation::contains_subrange(owner->data, 0, owner->len, index, index + 1)) using {
            0 <= index; index <= ((index + 1) as int32);
            ((index + 1) as int32) <= owner->len;
        };
    }
    have contains(memory(*owner), memory(owner->data)) by { normalize(); }
    have separate(memory(owner->data), memory(owner->data[index..index + 1])) by {
        apply(separation::separate_restrict(memory(*owner), memory(owner->data[0..owner->len]),
            memory(owner->data), memory(owner->data[index..index + 1]))) using {
            separate(memory(*owner), memory(owner->data[0..owner->len]));
            contains(memory(owner->data[0..owner->len]), memory(owner->data[index..index + 1]));
            contains(memory(*owner), memory(owner->data));
        };
    }
    have contains(memory(owner->data[index..index + 1]), memory(owner->data[index])) by { normalize(); }
    have contains(memory(owner->data), memory(owner->data)) by { normalize(); }
    have separate(memory(owner->data), memory(owner->data[index])) by {
        apply(separation::separate_restrict(memory(owner->data), memory(owner->data[index..index + 1]),
            memory(owner->data), memory(owner->data[index]))) using {
            separate(memory(owner->data), memory(owner->data[index..index + 1]));
            contains(memory(owner->data[index..index + 1]), memory(owner->data[index]));
            contains(memory(owner->data), memory(owner->data));
        };
    }
    have index < owner->len by { solve(); }
    have contains(memory(owner->data[0..owner->len]), memory(owner->data[index])) by {
        apply(separation::contains_element(owner->data, 0, owner->len, index)) using { 0 <= index; index < owner->len; };
    }
    have separate(memory(owner->data[index]), memory(*owner)) by { solve(); }
    step();
    have separate(statement(0).footprint, memory(owner->data)) by {
        normalize() using {
            at(before_store, separate(memory(owner->data), memory(owner->data[index])));
        };
    }
    have owner->data == at(before_store, owner->data) by {
        preserve(memory(owner->data), statement(0));
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
    have 0 <= index;
    mark before_store;
    have index <= ((index + 1) as int32);
    have ((index + 1) as int32) <= owner->len;
    have contains(memory(owner->data[0..owner->len]), memory(owner->data[index..index + 1])) by {
        apply(separation::contains_subrange(owner->data, 0, owner->len, index, index + 1)) using {
            0 <= index; index <= ((index + 1) as int32);
            ((index + 1) as int32) <= owner->len;
        };
    }
    have contains(memory(*owner), memory(owner->data)) by { normalize(); }
    have separate(memory(owner->data), memory(owner->data[index..index + 1])) by {
        apply(separation::separate_restrict(memory(*owner), memory(owner->data[0..owner->len]),
            memory(owner->data), memory(owner->data[index..index + 1]))) using {
            separate(memory(*owner), memory(owner->data[0..owner->len]));
            contains(memory(owner->data[0..owner->len]), memory(owner->data[index..index + 1]));
            contains(memory(*owner), memory(owner->data));
        };
    }
    have contains(memory(owner->data[index..index + 1]), memory(owner->data[index])) by { normalize(); }
    have contains(memory(owner->data), memory(owner->data)) by { normalize(); }
    have separate(memory(owner->data), memory(owner->data[index])) by {
        apply(separation::separate_restrict(memory(owner->data), memory(owner->data[index..index + 1]),
            memory(owner->data), memory(owner->data[index]))) using {
            separate(memory(owner->data), memory(owner->data[index..index + 1]));
            contains(memory(owner->data[index..index + 1]), memory(owner->data[index]));
            contains(memory(owner->data), memory(owner->data));
        };
    }
    have index < owner->len by { solve(); }
    have contains(memory(owner->data[0..owner->len]), memory(owner->data[index])) by {
        apply(separation::contains_element(owner->data, 0, owner->len, index)) using { 0 <= index; index < owner->len; };
    }
    have separate(memory(owner->data[index]), memory(*owner)) by { solve(); }
    step();
    have separate(statement(0).footprint, memory(owner->data)) by {
        normalize() using {
            at(before_store, separate(memory(owner->data), memory(owner->data[index])));
        };
    }
    have owner->data == at(before_store, owner->data) by {
        preserve(memory(owner->data), statement(0));
    }
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
    step();
    unfold(owned_split_buffer(owner));
    step();
    step();
    have owner->split == 1 by { known(); }
    have owner->len == length by { known(); }
    have owner->data == data by { known(); }
    have 1 < length by {
        solve() using { at(function.entry, 2 <= length); };
    }
    have 1 < owner->len by {
        known();
    }
    step();
    step();
    have owner->data == data by { known(); }
    have 1 < owner->len by { known(); }
    have data[1] == right_value by {
        normalize() using {
            at(statement(5).entry, *(owner->data + 1)) == at(statement(5).entry, right_value);
            owner->data == data;
        };
    }
    step();
    step();
    have separate(memory(owner->split), memory(data[1])) by { solve(); }
    have separate(statement(5).call(0).footprint, memory(data[1])) by {
        normalize() using { separate(memory(owner->split), memory(data[1])); };
    }
    have at(statement(5).call(0).exit, data[1]) == at(statement(5).call(0).entry, data[1]) by {
        preserve(memory(data[1]), statement(5).call(0));
    }
    have separate(memory(ignored), memory(data[1])) by { known(); }
    have separate(statement(5).assignment(ignored, 0).footprint, memory(data[1])) by {
        normalize() using { separate(memory(ignored), memory(data[1])); };
    }
    have at(statement(5).assignment(ignored, 0).exit, data[1]) == at(statement(5).assignment(ignored, 0).entry, data[1]) by {
        preserve(memory(data[1]), statement(5).assignment(ignored, 0));
    }
    have to_integer(at(statement(5).exit, owner->split)) == (to_integer(at(statement(5).entry, owner->split)) + 1) by {
        known();
    }
    apply(incremented_one_is_two(at(statement(5).entry, owner->split), at(statement(5).exit, owner->split))) using {
        at(statement(5).entry, owner->split) == 1;
        to_integer(at(statement(5).exit, owner->split)) == (to_integer(at(statement(5).entry,
            owner->split)) + 1);
    };
    fold(owned_split_buffer(owner));
    step();
    step();
    have separate(memory(result), memory(data[1])) by { known(); }
    have separate(statement(6).assignment(result, 0).footprint, memory(data[1])) by {
        normalize() using { separate(memory(result), memory(data[1])); };
    }
    have at(statement(6).assignment(result, 0).exit, data[1]) == at(statement(6).assignment(result, 0).entry, data[1]) by {
        preserve(memory(data[1]), statement(6).assignment(result, 0));
    }
    have data[1] == right_value by { known(); }
    apply(int32_equality_transitive(c(result), data[1], right_value)) using {
        c(result) == data[1];
        data[1] == right_value;
    };
    step();
    known();
    have owner->split == 2 by {
        known();
    }
    have owner->len == length by {
        known();
    }
    have owner->data == data by {
        known();
    }
    have data[0] == left_value by {
        rewrite(data, at(statement(3).entry, owner->data));
        known();
    }
    have data[1] == right_value by {
        known();
    }
    have result == right_value by {
        known();
    }
    known();
    known();
    known();
    known();
    known();
    known();
}
