import click::separation;

theorem selected_array_cell(whole: Resource, kept: Resource, p: int32*, len: int32, i: int32) {
    requires separate(whole, memory(p[0..len]));
    requires contains(whole, kept);
    requires 0 <= i;
    requires i < len;
    ensures separate(kept, memory(p[i])) by {
        have i <= 2147483646 by { solve() using { i < len; }; }
        have defined(i + 1) by { solve() using { 0 <= i; i <= 2147483646; }; }
        have i <= ((i + 1) as int32) by { solve() using { 0 <= i; i < len; }; }
        have ((i + 1) as int32) <= len by { solve() using { 0 <= i; i < len; }; }
        have contains(memory(p[0..len]), memory(p[i..i + 1])) by {
            apply(separation::contains_subrange(p, 0, len, i, i + 1)) using {
                defined(i + 1); 0 <= i; i <= ((i + 1) as int32); ((i + 1) as int32) <= len;
            };
        }
        have separate(kept, memory(p[i..i + 1])) by {
            apply(separation::separate_restrict(whole, memory(p[0..len]), kept, memory(p[i..i + 1]))) using {
                defined(i + 1); separate(whole, memory(p[0..len])); contains(whole, kept);
                contains(memory(p[0..len]), memory(p[i..i + 1]));
            };
        }
        have contains(kept, kept) by { normalize(); }
        have contains(memory(p[i..i + 1]), memory(p[i])) by { normalize(); }
        apply(separation::separate_restrict(kept, memory(p[i..i + 1]), kept, memory(p[i]))) using {
            defined(i + 1); separate(kept, memory(p[i..i + 1])); contains(kept, kept);
            contains(memory(p[i..i + 1]), memory(p[i]));
        };
    }
}

theorem int32_equality_transitive(first: int32, second: int32, third: int32) {
    requires first == second;
    requires second == third;

    ensures first == third by {
        solve();
    }
}

resource owned_segmented_buffer(owner: struct owned_segmented_buffer*) {
    owns *owner;
    owns owner->first_data[0..owner->first_len];
    owns owner->second_data[0..owner->second_len];
    fact 1 <= owner->first_len;
    fact 1 <= owner->second_len;
    fact separate(
        memory(*owner),
        memory(owner->first_data[0..owner->first_len])
    );
    fact separate(
        memory(*owner),
        memory(owner->second_data[0..owner->second_len])
    );
}

verifying "owned_segmented_buffer_init.c";
verifying "owned_segmented_buffer_get_first.c";
verifying "owned_segmented_buffer_set_first.c";
verifying "owned_segmented_buffer_set_second.c";
verifying "owned_segmented_buffer_swap.c";
verifying "owned_segmented_buffer_pipeline.c";

int32 owned_segmented_buffer_init(
    struct owned_segmented_buffer* owner,
    int32 first_data[],
    int32 first_len,
    int32 second_data[],
    int32 second_len
) {
    requires 1 <= first_len;
    requires 1 <= second_len;
    consumes *owner;
    consumes first_data[0..first_len];
    consumes second_data[0..second_len];
    produces owned_segmented_buffer(owner);
    ensures result == first_len;
    ensures owner->first_len == first_len;
    ensures owner->second_len == second_len;
    ensures 0 < owner->first_len;
    ensures 0 < owner->second_len;
    ensures owner->first_data == first_data;
    ensures owner->second_data == second_data;
} by {
    step();
    step();
    step();
    step();
    step();
    fold(owned_segmented_buffer(owner));
    have 0 < owner->first_len;
    have 0 < owner->second_len;
    known();
    known();
    known();
    known();
    known();
    known();
    known();
    known();
}

int32 owned_segmented_buffer_get_first(
    struct owned_segmented_buffer* owner,
    int32 index
) {
    requires 0 <= index;
    requires index < owner->first_len;
    views owned_segmented_buffer(owner);

    ensures result == owner->first_data[index];
} by {
    observe(owned_segmented_buffer(owner));
    step();
    known();
}

int32 owned_segmented_buffer_set_first(
    struct owned_segmented_buffer* owner,
    int32 index,
    int32 value
) {
    requires 0 <= index;
    requires index < owner->first_len;
    requires separate(
        memory(*owner),
        memory(owner->first_data[0..owner->first_len])
    );
    views *owner;
    owns owner->first_data[index..index + 1];
    ensures result == value;
    ensures owner->first_data[index] == value;
    ensures owner->first_len == old(owner->first_len);
    ensures owner->second_len == old(owner->second_len);
    ensures owner->first_data == old(owner->first_data);
    ensures owner->second_data == old(owner->second_data);
} by {
    mark before_store;
    have contains(memory(*owner), memory(owner->first_data)) by { normalize(); }
    have separate(memory(owner->first_data), memory(owner->first_data[index])) by {
        apply(selected_array_cell(memory(*owner), memory(owner->first_data), owner->first_data, owner->first_len, index)) using {
            separate(memory(*owner), memory(owner->first_data[0..owner->first_len]));
            contains(memory(*owner), memory(owner->first_data));
            0 <= index; index < owner->first_len;
        };
    }
    have contains(memory(*owner), memory(owner->second_data)) by { normalize(); }
    have separate(memory(owner->second_data), memory(owner->first_data[index])) by {
        apply(selected_array_cell(memory(*owner), memory(owner->second_data), owner->first_data, owner->first_len, index)) using {
            separate(memory(*owner), memory(owner->first_data[0..owner->first_len]));
            contains(memory(*owner), memory(owner->second_data));
            0 <= index; index < owner->first_len;
        };
    }
    have contains(memory(owner->first_data[0..owner->first_len]), memory(owner->first_data[index])) by {
        apply(separation::contains_element(owner->first_data, 0, owner->first_len, index)) using { 0 <= index; index < owner->first_len; };
    }
    have separate(memory(owner->first_data[index]), memory(*owner)) by { solve(); }
    step();
    have separate(statement(0).footprint, memory(owner->first_data)) by {
        solve() using { at(before_store, separate(memory(owner->first_data), memory(owner->first_data[index]))); };
    }
    have owner->first_data == at(before_store, owner->first_data) by {
        preserve(memory(owner->first_data), statement(0));
    }
    have separate(statement(0).footprint, memory(owner->second_data)) by {
        solve() using { at(before_store, separate(memory(owner->second_data), memory(owner->first_data[index]))); };
    }
    have owner->second_data == at(before_store, owner->second_data) by {
        preserve(memory(owner->second_data), statement(0));
    }
    step();
    solve();
}

int32 owned_segmented_buffer_set_second(
    struct owned_segmented_buffer* owner,
    int32 index,
    int32 value
) {
    requires 0 <= index;
    requires index < owner->second_len;
    requires separate(
        memory(*owner),
        memory(owner->second_data[0..owner->second_len])
    );
    views *owner;
    owns owner->second_data[index..index + 1];
    ensures result == value;
    ensures owner->second_data[index] == value;
    ensures owner->first_len == old(owner->first_len);
    ensures owner->second_len == old(owner->second_len);
    ensures owner->first_data == old(owner->first_data);
    ensures owner->second_data == old(owner->second_data);
} by {
    mark before_store;
    have contains(memory(*owner), memory(owner->first_data)) by { normalize(); }
    have separate(memory(owner->first_data), memory(owner->second_data[index])) by {
        apply(selected_array_cell(memory(*owner), memory(owner->first_data), owner->second_data, owner->second_len, index)) using {
            separate(memory(*owner), memory(owner->second_data[0..owner->second_len]));
            contains(memory(*owner), memory(owner->first_data));
            0 <= index; index < owner->second_len;
        };
    }
    have contains(memory(*owner), memory(owner->second_data)) by { normalize(); }
    have separate(memory(owner->second_data), memory(owner->second_data[index])) by {
        apply(selected_array_cell(memory(*owner), memory(owner->second_data), owner->second_data, owner->second_len, index)) using {
            separate(memory(*owner), memory(owner->second_data[0..owner->second_len]));
            contains(memory(*owner), memory(owner->second_data));
            0 <= index; index < owner->second_len;
        };
    }
    have contains(memory(owner->second_data[0..owner->second_len]), memory(owner->second_data[index])) by {
        apply(separation::contains_element(owner->second_data, 0, owner->second_len, index)) using { 0 <= index; index < owner->second_len; };
    }
    have separate(memory(owner->second_data[index]), memory(*owner)) by { solve(); }
    step();
    have separate(statement(0).footprint, memory(owner->first_data)) by {
        solve() using { at(before_store, separate(memory(owner->first_data), memory(owner->second_data[index]))); };
    }
    have owner->first_data == at(before_store, owner->first_data) by {
        preserve(memory(owner->first_data), statement(0));
    }
    have separate(statement(0).footprint, memory(owner->second_data)) by {
        solve() using { at(before_store, separate(memory(owner->second_data), memory(owner->second_data[index]))); };
    }
    have owner->second_data == at(before_store, owner->second_data) by {
        preserve(memory(owner->second_data), statement(0));
    }
    step();
    solve();
}

int32 owned_segmented_buffer_swap(struct owned_segmented_buffer* owner) {
    owns owned_segmented_buffer(owner);
    ensures result == old(owner->second_len);
    ensures owner->first_len == old(owner->second_len);
    ensures owner->second_len == old(owner->first_len);
    ensures 0 < owner->first_len;
    ensures 0 < owner->second_len;
    ensures owner->first_data == old(owner->second_data);
    ensures owner->second_data == old(owner->first_data);
} by {
    unfold(owned_segmented_buffer(owner));
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    have 1 <= owner->first_len by {
        known();
    }
    have 1 <= owner->second_len by {
        known();
    }
    have owner->first_data == old(owner->second_data);
    have owner->first_len == old(owner->second_len);
    have separate(memory(*owner), memory(owner->first_data[0..owner->first_len])) by {
        rewrite(owner->first_data, old(owner->second_data));
        rewrite(owner->first_len, old(owner->second_len));
        known();
    }
    have owner->second_data == old(owner->first_data);
    have owner->second_len == old(owner->first_len);
    have separate(memory(*owner), memory(owner->second_data[0..owner->second_len])) by {
        rewrite(owner->second_data, old(owner->first_data));
        rewrite(owner->second_len, old(owner->first_len));
        known();
    }
    fold(owned_segmented_buffer(owner));
    have 0 < owner->first_len by {
        have 0 < owner->first_len;
        known();
    }
    have 0 < owner->second_len by {
        have 0 < owner->second_len;
        known();
    }
    known();
    known();
    known();
    known();
    known();
}

int32 owned_segmented_buffer_pipeline(
    struct owned_segmented_buffer* owner,
    int32 first_data[],
    int32 first_len,
    int32 second_data[],
    int32 second_len,
    int32 first_value,
    int32 second_value
) {
    requires 1 <= first_len;
    requires 1 <= second_len;
    consumes *owner;
    consumes first_data[0..first_len];
    consumes second_data[0..second_len];
    produces owned_segmented_buffer(owner);
    ensures owner->first_len == first_len;
    ensures owner->second_len == second_len;
    ensures owner->first_data == first_data;
    ensures owner->second_data == second_data;
    ensures first_data[0] == first_value;
    ensures second_data[0] == second_value;
    ensures result == first_value;
} by {
    step();
    step();
    step();
    step();
    unfold(owned_segmented_buffer(owner));
    step();
    step();
    have at(statement(3).call(0).exit, first_data[0]) == first_value by {
        rewrite(first_data, at(statement(3).call(0).exit, owner->first_data));
        known();
    }
    have separate(memory(ignored), memory(first_data[0])) by { known(); }
    have separate(statement(3).assignment(ignored, 0).footprint, memory(first_data[0])) by {
        solve() using { separate(memory(ignored), memory(first_data[0])); };
    }
    have first_data[0] == at(statement(3).call(0).exit, first_data[0]) by {
        preserve(memory(first_data[0]), statement(3).assignment(ignored, 0));
    }
    have first_data[0] == first_value by { known(); }
    step();
    step();
    have owner->first_len == first_len by { known(); }
    have owner->second_len == second_len by { known(); }
    have 0 < owner->first_len by { known(); }
    have 0 < owner->second_len by { known(); }
    have separate(memory(second_data[0..1]), memory(first_data[0])) by { solve(); }
    have contains(memory(second_data[0..1]), statement(4).call(0).footprint) by {
        rewrite(second_data, at(statement(4).call(0).entry, owner->second_data));
        known();
    }
    have contains(memory(first_data[0]), memory(first_data[0])) by { normalize(); }
    have separate(statement(4).call(0).footprint, memory(first_data[0])) by {
        apply(separation::separate_restrict(memory(second_data[0..1]), memory(first_data[0]), statement(4).call(0).footprint, memory(first_data[0]))) using {
            separate(memory(second_data[0..1]), memory(first_data[0]));
            contains(memory(second_data[0..1]), statement(4).call(0).footprint);
            contains(memory(first_data[0]), memory(first_data[0]));
        };
    }
    have at(statement(4).call(0).exit, first_data[0]) == at(statement(4).call(0).entry, first_data[0]) by {
        preserve(memory(first_data[0]), statement(4).call(0));
    }
    have separate(memory(ignored), memory(first_data[0])) by { known(); }
    have separate(statement(4).assignment(ignored, 0).footprint, memory(first_data[0])) by {
        solve() using { separate(memory(ignored), memory(first_data[0])); };
    }
    have at(statement(4).assignment(ignored, 0).exit, first_data[0]) == at(statement(4).assignment(ignored, 0).entry, first_data[0]) by {
        preserve(memory(first_data[0]), statement(4).assignment(ignored, 0));
    }
    have first_data[0] == first_value by { known(); }
    have owner->first_data == first_data by { known(); }
    have owner->second_data == second_data by { known(); }
    have at(statement(5).entry, second_data[0]) == at(statement(5).entry, second_value) by {
        rewrite(at(statement(5).entry, second_value), at(statement(5).entry, owner->second_data[0]));
        rewrite(at(statement(5).entry, owner->second_data), at(statement(5).entry, second_data));
        known();
    }
    have second_data[0] == second_value by { known(); }
    fold(owned_segmented_buffer(owner));
    step();
    step();
    have first_data[0] == first_value by { known(); }
    apply(int32_equality_transitive(program::result, first_data[0], first_value)) using {
        program::result == first_data[0];
        *first_data == first_value;
    };
    step();
    have owner->first_data == first_data;
    known();
    known();
    known();
    known();
    known();
    known();
    known();
    known();
}
