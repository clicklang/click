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
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
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
    assumption();
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
    have separate(memory(owner->first_data[index]), memory(owner->first_data));
    step();
    have separate(statement(0).footprint, memory(owner->first_data)) by {
        normalize() using {
            at(before_store, separate(memory(owner->first_data[index]), memory(owner->first_data)));
        };
    }
    have owner->first_data == at(before_store, owner->first_data) by {
        transport_certificate {
            premise 0: separate(statement(0).footprint, memory(owner->first_data))
                => separate(statement(0).footprint, memory(owner->first_data));
            preserve 0 => owner->first_data == at(before_store, owner->first_data);
            conclusion 1;
        }
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
    step();
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
        assumption();
    }
    have 1 <= owner->second_len by {
        assumption();
    }
    have owner->first_data == old(owner->second_data);
    have owner->first_len == old(owner->second_len);
    have separate(memory(*owner), memory(owner->first_data[0..owner->first_len])) by {
        rewrite(owner->first_data == old(owner->second_data));
        rewrite(owner->first_len == old(owner->second_len));
        assumption();
    }
    have owner->second_data == old(owner->first_data);
    have owner->second_len == old(owner->first_len);
    have separate(memory(*owner), memory(owner->second_data[0..owner->second_len])) by {
        rewrite(owner->second_data == old(owner->first_data));
        rewrite(owner->second_len == old(owner->first_len));
        assumption();
    }
    fold(owned_segmented_buffer(owner));
    have 0 < owner->first_len by {
        have 0 < owner->first_len;
        assumption();
    }
    have 0 < owner->second_len by {
        have 0 < owner->second_len;
        assumption();
    }
    assumption();
    normalize();
    assumption();
    assumption();
    assumption();
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
    unfold(owned_segmented_buffer(owner));
    step();
    have at(region(4).entry, first_data[0]) == at(region(4).entry, first_value) by {
        rewrite(at(region(4).entry, first_value) == at(region(4).entry, owner->first_data[0]));
        rewrite(at(region(4).entry, owner->first_data) == at(region(4).entry, first_data));
        normalize();
    }
    transport(at(region(4).entry, first_data[0]) == at(region(4).entry, first_value), first_data[0] == first_value) using {
        at(region(4).entry, first_data[0]) == at(region(4).entry, first_value);
    };
    step();
    transport(at(region(4).entry, owner->first_len) == at(region(4).entry, first_len), owner->first_len == first_len) using {
        1 <= second_len;
        at(region(4).entry, owner->first_len) == first_len;
        at(region(4).entry, owner->second_data) == second_data;
    };
    transport(at(region(4).entry, owner->second_len) == at(region(4).entry, second_len), owner->second_len == second_len) using {
        1 <= second_len;
        at(region(4).entry, owner->second_len) == second_len;
        at(region(4).entry, owner->second_data) == second_data;
    };
    transport(at(region(4).entry, 0) < at(region(4).entry, owner->first_len), 0 < owner->first_len) using {
        0 < at(region(4).entry, owner->first_len);
        1 <= second_len;
        at(region(4).entry, owner->second_data) == second_data;
    };
    transport(at(region(4).entry, 0) < at(region(4).entry, owner->second_len), 0 < owner->second_len) using {
        0 < at(region(4).entry, owner->second_len);
        at(region(4).entry, owner->second_len) == second_len;
        at(region(4).entry, owner->second_data) == second_data;
    };
    transport(at(region(4).entry, first_data[0]) == at(region(4).entry, first_value), first_data[0] == first_value) using {
        1 <= first_len;
        1 <= second_len;
        at(region(4).entry, first_data[0]) == first_value;
        at(region(4).entry, owner->second_data) == second_data;
    };
    transport(at(region(4).entry, owner->first_data) == at(region(4).entry, first_data), owner->first_data == first_data) using {
        1 <= second_len;
        at(region(4).entry, owner->first_data) == first_data;
        at(region(4).entry, owner->second_data) == second_data;
    };
    transport(at(region(4).entry, owner->second_data) == at(region(4).entry, second_data), owner->second_data == second_data) using {
        at(region(4).entry, owner->second_data) == at(region(4).entry, second_data);
        1 <= second_len;
    };
    have at(region(5).entry, second_data[0]) == at(region(5).entry, second_value) by {
        rewrite(at(region(5).entry, second_value) == at(region(5).entry, owner->second_data[0]));
        rewrite(at(region(5).entry, owner->second_data) == at(region(5).entry, second_data));
        normalize();
    }
    transport(at(region(5).entry, second_data[0]) == at(region(5).entry, second_value), second_data[0] == second_value) using {
        at(region(5).entry, second_data[0]) == at(region(5).entry, second_value);
    };
    fold(owned_segmented_buffer(owner));
    step();
    have c(result) == first_data[0] by {
        rewrite(at(region(6).entry, c(result)) == at(region(6).entry, owner->first_data[0]));
        rewrite(owner->first_data == first_data);
        normalize();
    }
    apply(int32_equality_transitive(c(result), first_data[0], first_value)) using {
        c(result) == first_data[0];
        *first_data == first_value;
    };
    step();
    have owner->first_data == first_data;
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
}
