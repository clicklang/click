# Symbolic-index store keeps a cell a recorded order separates

The proof uses the strict index order to establish separation, then explicitly
preserves the terminator across the selected store before refolding its owner.

```c filename=set_then_read_end.c
int32 set_then_read_end(int32* data, int32 index, int32 len, int32 cap) {
    int32 value;
    data[index] = 1;
    value = data[len];
    return value;
}
```

```click
predicate terminated_at(data: int32[], length: int32) {
    data[length] == 0
}

resource zero_terminated(data: int32*, len: int32, cap: int32) {
    owns data[0..cap];
    fact 0 <= len;
    fact len < cap;
    fact terminated_at(data, len);
}

verifying "set_then_read_end.c";

int32 set_then_read_end(int32* data, int32 index, int32 len, int32 cap) {
    requires 0 <= index;
    requires index < len;
    owns zero_terminated(data, len, cap);
    ensures result == 0;
} by {
    unfold(zero_terminated(data, len, cap));
    unfold(at(function.entry, terminated_at(data, len)));
    have index < cap;
    step();
    step();
    have index != len by { solve() using { index < len; }; }
    have separate(memory(data[index]), memory(data[len])) by {
        apply(click::separation::separate_elements(data, index, len)) using { index != len; };
    }
    have separate(statement(1).footprint, memory(data[len])) by {
        solve() using { separate(memory(data[index]), memory(data[len])); };
    }
    have separate(statement(0).footprint, memory(data[len])) by { solve() using {}; }
    have at(statement(0).exit, data[len]) == at(statement(0).entry, data[len]) by {
        preserve(memory(data[len]), statement(0));
    }
    have at(statement(1).exit, data[len]) == at(statement(1).entry, data[len]) by {
        preserve(memory(data[len]), statement(1));
    }
    have terminated_at(data, len) by {
        unfold(terminated_at(data, len));
        known();
    }
    step();
    fold(zero_terminated(data, len, cap));
    step();
    solve();
}
```

```expect
pass
```
