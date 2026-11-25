import click::separation;

theorem selected_array_cell(whole: Resource, kept: Resource, p: int32*, len: int32, i: int32) {
    requires separate(whole, memory(p[0..len]));
    requires contains(whole, kept);
    requires 0 <= i;
    requires i < len;
    ensures separate(kept, memory(p[i])) by {
        have contains(memory(p[0..len]), memory(p[i])) by {
            apply(separation::contains_element(p, 0, len, i));
        }
        apply(separation::separate_restrict(whole, memory(p[0..len]), kept, memory(p[i])));
    }
}

theorem int32_equality_transitive(first: int32, second: int32, third: int32) {
    requires first == second;
    requires second == third;

    ensures first == third by {
        close();
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
    close();
    close();
    close();
    close();
    close();
    close();
    close();
    close();
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
    close();
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
    have contains(memory(*owner), memory(owner->first_data)) by { close(); }
    have separate(memory(owner->first_data), memory(owner->first_data[index])) by {
        apply(selected_array_cell(memory(*owner), memory(owner->first_data), owner->first_data, owner->first_len, index));
    }
    have contains(memory(*owner), memory(owner->second_data)) by { close(); }
    have separate(memory(owner->second_data), memory(owner->first_data[index])) by {
        apply(selected_array_cell(memory(*owner), memory(owner->second_data), owner->first_data, owner->first_len, index));
    }
    have contains(memory(owner->first_data[0..owner->first_len]), memory(owner->first_data[index])) by {
        apply(separation::contains_element(owner->first_data, 0, owner->first_len, index));
    }
    have separate(memory(owner->first_data[index]), memory(*owner)) by { close(); }
    apply(separation::contains_refl(memory(owner->first_data[index])));
    have contains(memory(*owner), memory(owner->first_len)) by { close(); }
    have separate(memory(owner->first_data[index]), memory(owner->first_len)) by {
        apply(separation::separate_restrict(memory(owner->first_data[index]), memory(*owner),
            memory(owner->first_data[index]), memory(owner->first_len)));
    }
    have contains(memory(*owner), memory(owner->second_len)) by { close(); }
    have separate(memory(owner->first_data[index]), memory(owner->second_len)) by {
        apply(separation::separate_restrict(memory(owner->first_data[index]), memory(*owner),
            memory(owner->first_data[index]), memory(owner->second_len)));
    }
    step();
    have separate(statement(0).footprint, memory(owner->first_data)) by {
        close() using { at(before_store, separate(memory(owner->first_data), memory(owner->first_data[index]))); };
    }
    have owner->first_data == at(before_store, owner->first_data) by {
        preserve(memory(owner->first_data), statement(0));
    }
    have separate(statement(0).footprint, memory(owner->second_data)) by {
        close() using { at(before_store, separate(memory(owner->second_data), memory(owner->first_data[index]))); };
    }
    have owner->second_data == at(before_store, owner->second_data) by {
        preserve(memory(owner->second_data), statement(0));
    }
    have separate(statement(0).footprint, memory(owner->first_len)) by {
        close() using { at(before_store, separate(memory(owner->first_data[index]), memory(owner->first_len))); };
    }
    have owner->first_len == old(owner->first_len) by {
        preserve(memory(owner->first_len), statement(0));
    }
    have separate(statement(0).footprint, memory(owner->second_len)) by {
        close() using { at(before_store, separate(memory(owner->first_data[index]), memory(owner->second_len))); };
    }
    have owner->second_len == old(owner->second_len) by {
        preserve(memory(owner->second_len), statement(0));
    }
    step();
    close();
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
    have contains(memory(*owner), memory(owner->first_data)) by { close(); }
    have separate(memory(owner->first_data), memory(owner->second_data[index])) by {
        apply(selected_array_cell(memory(*owner), memory(owner->first_data), owner->second_data, owner->second_len, index));
    }
    have contains(memory(*owner), memory(owner->second_data)) by { close(); }
    have separate(memory(owner->second_data), memory(owner->second_data[index])) by {
        apply(selected_array_cell(memory(*owner), memory(owner->second_data), owner->second_data, owner->second_len, index));
    }
    have contains(memory(owner->second_data[0..owner->second_len]), memory(owner->second_data[index])) by {
        apply(separation::contains_element(owner->second_data, 0, owner->second_len, index));
    }
    have separate(memory(owner->second_data[index]), memory(*owner)) by { close(); }
    apply(separation::contains_refl(memory(owner->second_data[index])));
    have contains(memory(*owner), memory(owner->first_len)) by { close(); }
    have separate(memory(owner->second_data[index]), memory(owner->first_len)) by {
        apply(separation::separate_restrict(memory(owner->second_data[index]), memory(*owner),
            memory(owner->second_data[index]), memory(owner->first_len)));
    }
    have contains(memory(*owner), memory(owner->second_len)) by { close(); }
    have separate(memory(owner->second_data[index]), memory(owner->second_len)) by {
        apply(separation::separate_restrict(memory(owner->second_data[index]), memory(*owner),
            memory(owner->second_data[index]), memory(owner->second_len)));
    }
    step();
    have separate(statement(0).footprint, memory(owner->first_data)) by {
        close() using { at(before_store, separate(memory(owner->first_data), memory(owner->second_data[index]))); };
    }
    have owner->first_data == at(before_store, owner->first_data) by {
        preserve(memory(owner->first_data), statement(0));
    }
    have separate(statement(0).footprint, memory(owner->second_data)) by {
        close() using { at(before_store, separate(memory(owner->second_data), memory(owner->second_data[index]))); };
    }
    have owner->second_data == at(before_store, owner->second_data) by {
        preserve(memory(owner->second_data), statement(0));
    }
    have separate(statement(0).footprint, memory(owner->first_len)) by {
        close() using { at(before_store, separate(memory(owner->second_data[index]), memory(owner->first_len))); };
    }
    have owner->first_len == old(owner->first_len) by {
        preserve(memory(owner->first_len), statement(0));
    }
    have separate(statement(0).footprint, memory(owner->second_len)) by {
        close() using { at(before_store, separate(memory(owner->second_data[index]), memory(owner->second_len))); };
    }
    have owner->second_len == old(owner->second_len) by {
        preserve(memory(owner->second_len), statement(0));
    }
    step();
    close();
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
        close();
    }
    have 1 <= owner->second_len by {
        close();
    }
    have owner->first_data == old(owner->second_data);
    have owner->first_len == old(owner->second_len);
    have separate(memory(*owner), memory(owner->first_data[0..owner->first_len])) by {
        rewrite(owner->first_data, old(owner->second_data));
        rewrite(owner->first_len, old(owner->second_len));
        close();
    }
    have owner->second_data == old(owner->first_data);
    have owner->second_len == old(owner->first_len);
    have separate(memory(*owner), memory(owner->second_data[0..owner->second_len])) by {
        rewrite(owner->second_data, old(owner->first_data));
        rewrite(owner->second_len, old(owner->first_len));
        close();
    }
    fold(owned_segmented_buffer(owner));
    have 0 < owner->first_len by {
        have 0 < owner->first_len;
        close();
    }
    have 0 < owner->second_len by {
        have 0 < owner->second_len;
        close();
    }
    close();
    close();
    close();
    close();
    close();
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
        close();
    }
    have separate(memory(ignored), memory(first_data[0])) by { close(); }
    have separate(statement(3).assignment(ignored, 0).footprint, memory(first_data[0])) by {
        close() using { separate(memory(ignored), memory(first_data[0])); };
    }
    have first_data[0] == at(statement(3).call(0).exit, first_data[0]) by {
        preserve(memory(first_data[0]), statement(3).assignment(ignored, 0));
    }
    have first_data[0] == first_value by { close(); }
    step();
    step();
    have owner->first_len == first_len by { close(); }
    have owner->second_len == second_len by { close(); }
    have 0 < owner->first_len by { close(); }
    have 0 < owner->second_len by { close(); }
    have separate(memory(second_data[0..1]), memory(first_data[0])) by { close(); }
    have contains(memory(second_data[0..1]), statement(4).call(0).footprint) by {
        rewrite(second_data, at(statement(4).call(0).entry, owner->second_data));
        close();
    }
    have contains(memory(first_data[0]), memory(first_data[0])) by { apply(click::separation::contains_refl(memory(first_data[0]))); }
    have separate(statement(4).call(0).footprint, memory(first_data[0])) by {
        apply(separation::separate_restrict(memory(second_data[0..1]), memory(first_data[0]), statement(4).call(0).footprint, memory(first_data[0])));
    }
    have at(statement(4).call(0).exit, first_data[0]) == at(statement(4).call(0).entry, first_data[0]) by {
        preserve(memory(first_data[0]), statement(4).call(0));
    }
    have separate(memory(ignored), memory(first_data[0])) by { close(); }
    have separate(statement(4).assignment(ignored, 0).footprint, memory(first_data[0])) by {
        close() using { separate(memory(ignored), memory(first_data[0])); };
    }
    have at(statement(4).assignment(ignored, 0).exit, first_data[0]) == at(statement(4).assignment(ignored, 0).entry, first_data[0]) by {
        preserve(memory(first_data[0]), statement(4).assignment(ignored, 0));
    }
    have first_data[0] == first_value by { close(); }
    have owner->first_data == first_data by { close(); }
    have owner->second_data == second_data by { close(); }
    have at(statement(5).entry, second_data[0]) == at(statement(5).entry, second_value) by {
        rewrite(at(statement(5).entry, second_value), at(statement(5).entry, owner->second_data[0]));
        rewrite(at(statement(5).entry, owner->second_data), at(statement(5).entry, second_data));
        close();
    }
    have second_data[0] == second_value by { close(); }
    fold(owned_segmented_buffer(owner));
    step();
    step();
    have first_data[0] == first_value by { close(); }
    apply(int32_equality_transitive(program::result, first_data[0], first_value));
    step();
    have owner->first_data == first_data;
    close();
    close();
    close();
    close();
    close();
    close();
    close();
    close();
}
